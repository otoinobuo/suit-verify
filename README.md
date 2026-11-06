# suit-verify

A note on version comparison in draft-ietf-suit-update-management-16, Section 4.4.

Summary: https://ba-cybersecurity.com/research/suit-version-comparison/

## Start here: one case, about a minute, no tools

Section 4.4.1 of the draft gives this encoding:

    1.2.3-alpha.4 = [1,2,3,-3,4]

and says the negative indicators let pre-releases "compare correctly with final
releases". Section 4.4 says comparison "stops after all integers in the array
defined by the manifest have been consumed".

Take the condition `Equal [1,2,3]` and a component at 1.2.3-alpha.4:

    1 = 1, 2 = 2, 3 = 3, the manifest's array is consumed, stop: the condition matches.

So a condition for release 1.2.3 also accepts its alpha. `Greater or Equal [1,2,3]`
accepts it the same way, and `Lesser [1,2,3]` does not, although SemVer 2.0.0
Section 11 (a normative reference of the draft) ranks 1.2.3-alpha.4 below 1.2.3.

If that reading is wrong, or this is intended, nothing below matters.

The same case in a few lines of Lean 4 (core only, runs in under a second):
[`lean/Minimal.lean`](lean/Minimal.lean).

## Details, if the case above is of interest

**Other cases** (manifest value first):

| Condition | Component | Section 4.4 | SemVer |
|---|---|---|---|
| Equal [2,0,0] | [2,0,0,-1,1] (2.0.0-rc.1) | matches | rc.1 is lower |
| Lesser [1,10,0] | [1,10,0,-1,1] | does not match | rc.1 is lower |
| Equal [1,2,-2] | [1,2,0,-2] (both 1.2.0-beta) | does not match | same version |
| Equal [2,0,0,-1] | [2,0,0,-1,1] | matches | rc is lower than rc.1 |

**One possible wording for a fix** (it keeps "Equal [1] matches all versions
starting with 1"):

> Before comparison, the release part of the component's version, and of a manifest
> value that is followed by a pre-release indicator, is padded with zeros to three
> integers; integers are then compared in sequence, and when one array ends without
> a difference, the version whose next integer is a pre-release indicator is Lesser,
> the version that has further pre-release identifiers is Greater, and otherwise (the
> manifest's array ended within its release part) the versions compare as Equal.

**Checks**

- `lean/SuitVersion.lean`: the rule as written (`draftCmp`), the cases above by
  `decide`, and `fixedCmp_sound`, which proves that the wording above agrees with
  SemVer precedence, and with the prefix rule for short manifest arrays, for any
  array length and any integer values. No `sorry`; axioms are printed at the end of
  the file. What this cannot show is that `draftCmp` reads Section 4.4 correctly,
  so please judge that by reading those 4 lines.
- `model/suitver.py`: every pair of 858 arrays under 5 operators (3,680,820
  combinations). The current text differs from SemVer in 49,365 of them, the wording
  above in none. `model/breakdown.py` splits these by cause.
- `lean/CrossCheck.lean`: 80 pairs computed by the Python model, rechecked in Lean.

**Not claimed.** This is not a break of any cryptographic mechanism, and no attack on
a deployed device was tried. Implementations were not tested.

## The encoding proposed on the list (1 Nov 2026 UTC)

[Brendan Moran's message](https://mailarchive.ietf.org/arch/msg/suit/x0npYlbvfSzW9Kj8pln6hugI6MY) keeps the
comparison rule and changes the encoding: three release integers, then 0 for a final release, or a negative stage,
its identifiers and the end marker -24.

- `lean/MoranEncoding.lean`: `moran_sound` proves that for complete versions the unchanged rule gives SemVer
  precedence and is always defined, for any integer values and any number of identifiers. No `sorry`.
- `model/moran.py`: 1,728 versions and every pair under 5 operators (14,929,920 combinations): 0 disagreements
  with SemVer and 0 cases where the component ends first. Output: `model/moran_out.txt`.

Short selectors keep the prefix behaviour by design, so `Greater or Equal [1,0]` accepts 1.0.0-alpha and
`Lesser [1,10]` does not accept 1.10.0-rc. Outside the Section 4.4.1 mapping, a component shorter than the
manifest (`[2025,12,6]` against `[2025,12]`) still has no defined outcome, and neither does a component still
reporting the -16 form (`[1,2,3]` against `[1,2,3,0]`).

## Reproduce

    lean lean/Minimal.lean                 # Lean 4.33.1, prints nothing
    lean lean/SuitVersion.lean             # prints only the axioms line
    lean -o /tmp/SuitVersion.olean lean/SuitVersion.lean
    LEAN_PATH=/tmp lean lean/CrossCheck.lean
    python3 model/suitver.py
    python3 model/breakdown.py
    lean lean/MoranEncoding.lean           # prints only the axioms line
    python3 model/moran.py

## Credits and license

Nobuo Otoi, ba-cybersecurity.com. The models and proofs were written with an AI coding
assistant. Apache License 2.0.
