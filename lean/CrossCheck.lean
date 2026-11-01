import SuitVersion

/-! Results computed by model/suitver.py (gen_crosscheck.py), re-checked by `decide`. -/

example : draftCmp [2,0,0] [2,0,0,-1,1] = some .eq := by decide
example : fixedCmp ⟨[2,0,0], none⟩ ⟨[2,0,0], some ⟨-1,[1]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,0,0], none⟩ ⟨[2,0,0], some ⟨-1,[1]⟩⟩ = .lt := by decide
example : draftCmp [1,10,0] [1,10,0,-1,1] = some .eq := by decide
example : fixedCmp ⟨[1,10,0], none⟩ ⟨[1,10,0], some ⟨-1,[1]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,10,0], none⟩ ⟨[1,10,0], some ⟨-1,[1]⟩⟩ = .lt := by decide
example : draftCmp [1,2,-2] [1,2,0,-2] = some .gt := by decide
example : fixedCmp ⟨[1,2], some ⟨-2,[]⟩⟩ ⟨[1,2,0], some ⟨-2,[]⟩⟩ = .eq := by decide
example : refCmp ⟨[1,2], some ⟨-2,[]⟩⟩ ⟨[1,2,0], some ⟨-2,[]⟩⟩ = .eq := by decide
example : draftCmp [1,2,0,-2] [1,2,-2] = some .lt := by decide
example : fixedCmp ⟨[1,2,0], some ⟨-2,[]⟩⟩ ⟨[1,2], some ⟨-2,[]⟩⟩ = .eq := by decide
example : refCmp ⟨[1,2,0], some ⟨-2,[]⟩⟩ ⟨[1,2], some ⟨-2,[]⟩⟩ = .eq := by decide
example : draftCmp [2,0,0,-1] [2,0,0,-1,1] = some .eq := by decide
example : fixedCmp ⟨[2,0,0], some ⟨-1,[]⟩⟩ ⟨[2,0,0], some ⟨-1,[1]⟩⟩ = .gt := by decide
example : refCmp ⟨[2,0,0], some ⟨-1,[]⟩⟩ ⟨[2,0,0], some ⟨-1,[1]⟩⟩ = .gt := by decide
example : draftCmp [2,0,0,-1,1] [2,0,0,-1] = none := by decide
example : fixedCmp ⟨[2,0,0], some ⟨-1,[1]⟩⟩ ⟨[2,0,0], some ⟨-1,[]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,0,0], some ⟨-1,[1]⟩⟩ ⟨[2,0,0], some ⟨-1,[]⟩⟩ = .lt := by decide
example : draftCmp [1,2,3] [1,2] = none := by decide
example : fixedCmp ⟨[1,2,3], none⟩ ⟨[1,2], none⟩ = .lt := by decide
example : refCmp ⟨[1,2,3], none⟩ ⟨[1,2], none⟩ = .lt := by decide
example : draftCmp [2,0] [2,0,-1,1] = some .eq := by decide
example : fixedCmp ⟨[2,0], none⟩ ⟨[2,0], some ⟨-1,[1]⟩⟩ = .eq := by decide
example : refCmp ⟨[2,0], none⟩ ⟨[2,0], some ⟨-1,[1]⟩⟩ = .eq := by decide
example : draftCmp [2,0,0] [2,0,-1,1] = some .lt := by decide
example : fixedCmp ⟨[2,0,0], none⟩ ⟨[2,0], some ⟨-1,[1]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,0,0], none⟩ ⟨[2,0], some ⟨-1,[1]⟩⟩ = .lt := by decide
example : draftCmp [1] [1,0,0,-3] = some .eq := by decide
example : fixedCmp ⟨[1], none⟩ ⟨[1,0,0], some ⟨-3,[]⟩⟩ = .eq := by decide
example : refCmp ⟨[1], none⟩ ⟨[1,0,0], some ⟨-3,[]⟩⟩ = .eq := by decide
example : draftCmp [1,0] [1,0,0,-3] = some .eq := by decide
example : fixedCmp ⟨[1,0], none⟩ ⟨[1,0,0], some ⟨-3,[]⟩⟩ = .eq := by decide
example : refCmp ⟨[1,0], none⟩ ⟨[1,0,0], some ⟨-3,[]⟩⟩ = .eq := by decide
example : draftCmp [1,0,0] [1,0,0,-3] = some .eq := by decide
example : fixedCmp ⟨[1,0,0], none⟩ ⟨[1,0,0], some ⟨-3,[]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,0,0], none⟩ ⟨[1,0,0], some ⟨-3,[]⟩⟩ = .lt := by decide
example : draftCmp [0] [1,-1] = some .gt := by decide
example : fixedCmp ⟨[0], none⟩ ⟨[1], some ⟨-1,[]⟩⟩ = .gt := by decide
example : refCmp ⟨[0], none⟩ ⟨[1], some ⟨-1,[]⟩⟩ = .gt := by decide
example : draftCmp [1,2] [1,3,0,-2,5] = some .gt := by decide
example : fixedCmp ⟨[1,2], none⟩ ⟨[1,3,0], some ⟨-2,[5]⟩⟩ = .gt := by decide
example : refCmp ⟨[1,2], none⟩ ⟨[1,3,0], some ⟨-2,[5]⟩⟩ = .gt := by decide
example : draftCmp [1,1,0,-3,0,0] [0,2,2,-2,1,0] = some .lt := by decide
example : fixedCmp ⟨[1,1,0], some ⟨-3,[0,0]⟩⟩ ⟨[0,2,2], some ⟨-2,[1,0]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,1,0], some ⟨-3,[0,0]⟩⟩ ⟨[0,2,2], some ⟨-2,[1,0]⟩⟩ = .lt := by decide
example : draftCmp [2,1,-2,0,0] [1,2,2,-3,0] = some .lt := by decide
example : fixedCmp ⟨[2,1], some ⟨-2,[0,0]⟩⟩ ⟨[1,2,2], some ⟨-3,[0]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,1], some ⟨-2,[0,0]⟩⟩ ⟨[1,2,2], some ⟨-3,[0]⟩⟩ = .lt := by decide
example : draftCmp [0,1,1,-1,0,1] [1,0,0,-2,0] = some .gt := by decide
example : fixedCmp ⟨[0,1,1], some ⟨-1,[0,1]⟩⟩ ⟨[1,0,0], some ⟨-2,[0]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,1,1], some ⟨-1,[0,1]⟩⟩ ⟨[1,0,0], some ⟨-2,[0]⟩⟩ = .gt := by decide
example : draftCmp [0,0,1,-1,0,0] [1,2,-2,0] = some .gt := by decide
example : fixedCmp ⟨[0,0,1], some ⟨-1,[0,0]⟩⟩ ⟨[1,2], some ⟨-2,[0]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,0,1], some ⟨-1,[0,0]⟩⟩ ⟨[1,2], some ⟨-2,[0]⟩⟩ = .gt := by decide
example : draftCmp [2,1,0,-2,0,1] [2,0,1,-3,0,1] = some .lt := by decide
example : fixedCmp ⟨[2,1,0], some ⟨-2,[0,1]⟩⟩ ⟨[2,0,1], some ⟨-3,[0,1]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,1,0], some ⟨-2,[0,1]⟩⟩ ⟨[2,0,1], some ⟨-3,[0,1]⟩⟩ = .lt := by decide
example : draftCmp [1,0,0,-1,1,1] [2,0,2,-1,0,1] = some .gt := by decide
example : fixedCmp ⟨[1,0,0], some ⟨-1,[1,1]⟩⟩ ⟨[2,0,2], some ⟨-1,[0,1]⟩⟩ = .gt := by decide
example : refCmp ⟨[1,0,0], some ⟨-1,[1,1]⟩⟩ ⟨[2,0,2], some ⟨-1,[0,1]⟩⟩ = .gt := by decide
example : draftCmp [0,2,1,-3,0] [0,1,-1] = some .lt := by decide
example : fixedCmp ⟨[0,2,1], some ⟨-3,[0]⟩⟩ ⟨[0,1], some ⟨-1,[]⟩⟩ = .lt := by decide
example : refCmp ⟨[0,2,1], some ⟨-3,[0]⟩⟩ ⟨[0,1], some ⟨-1,[]⟩⟩ = .lt := by decide
example : draftCmp [2,2,0,-2] [0,0,0,-2,1,0] = some .lt := by decide
example : fixedCmp ⟨[2,2,0], some ⟨-2,[]⟩⟩ ⟨[0,0,0], some ⟨-2,[1,0]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,2,0], some ⟨-2,[]⟩⟩ ⟨[0,0,0], some ⟨-2,[1,0]⟩⟩ = .lt := by decide
example : draftCmp [2,0,2,-2] [0,0,0,-1,1] = some .lt := by decide
example : fixedCmp ⟨[2,0,2], some ⟨-2,[]⟩⟩ ⟨[0,0,0], some ⟨-1,[1]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,0,2], some ⟨-2,[]⟩⟩ ⟨[0,0,0], some ⟨-1,[1]⟩⟩ = .lt := by decide
example : draftCmp [1,0,-3,0,0] [0,2,1,-3] = some .lt := by decide
example : fixedCmp ⟨[1,0], some ⟨-3,[0,0]⟩⟩ ⟨[0,2,1], some ⟨-3,[]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,0], some ⟨-3,[0,0]⟩⟩ ⟨[0,2,1], some ⟨-3,[]⟩⟩ = .lt := by decide
example : draftCmp [2,0,0,-2,1,1] [2,1,-3,0] = some .gt := by decide
example : fixedCmp ⟨[2,0,0], some ⟨-2,[1,1]⟩⟩ ⟨[2,1], some ⟨-3,[0]⟩⟩ = .gt := by decide
example : refCmp ⟨[2,0,0], some ⟨-2,[1,1]⟩⟩ ⟨[2,1], some ⟨-3,[0]⟩⟩ = .gt := by decide
example : draftCmp [1,0,2,-1,1,0] [1,0,-1,0,1] = some .lt := by decide
example : fixedCmp ⟨[1,0,2], some ⟨-1,[1,0]⟩⟩ ⟨[1,0], some ⟨-1,[0,1]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,0,2], some ⟨-1,[1,0]⟩⟩ ⟨[1,0], some ⟨-1,[0,1]⟩⟩ = .lt := by decide
example : draftCmp [2,2,-3,0,1] [0,1,1,-3,0,1] = some .lt := by decide
example : fixedCmp ⟨[2,2], some ⟨-3,[0,1]⟩⟩ ⟨[0,1,1], some ⟨-3,[0,1]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,2], some ⟨-3,[0,1]⟩⟩ ⟨[0,1,1], some ⟨-3,[0,1]⟩⟩ = .lt := by decide
example : draftCmp [1,2,0,-1,0,1] [0,1,-3,0,1] = some .lt := by decide
example : fixedCmp ⟨[1,2,0], some ⟨-1,[0,1]⟩⟩ ⟨[0,1], some ⟨-3,[0,1]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,2,0], some ⟨-1,[0,1]⟩⟩ ⟨[0,1], some ⟨-3,[0,1]⟩⟩ = .lt := by decide
example : draftCmp [2,1,2,-3,1,1] [2,2,-2] = some .gt := by decide
example : fixedCmp ⟨[2,1,2], some ⟨-3,[1,1]⟩⟩ ⟨[2,2], some ⟨-2,[]⟩⟩ = .gt := by decide
example : refCmp ⟨[2,1,2], some ⟨-3,[1,1]⟩⟩ ⟨[2,2], some ⟨-2,[]⟩⟩ = .gt := by decide
example : draftCmp [0,0,-3,1,0] [0,0,2,-2,0,1] = some .gt := by decide
example : fixedCmp ⟨[0,0], some ⟨-3,[1,0]⟩⟩ ⟨[0,0,2], some ⟨-2,[0,1]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,0], some ⟨-3,[1,0]⟩⟩ ⟨[0,0,2], some ⟨-2,[0,1]⟩⟩ = .gt := by decide
example : draftCmp [1,2,2,-3,0] [0,0,1] = some .lt := by decide
example : fixedCmp ⟨[1,2,2], some ⟨-3,[0]⟩⟩ ⟨[0,0,1], none⟩ = .lt := by decide
example : refCmp ⟨[1,2,2], some ⟨-3,[0]⟩⟩ ⟨[0,0,1], none⟩ = .lt := by decide
example : draftCmp [2,0,-1,0] [0,2,2,-2,1] = some .lt := by decide
example : fixedCmp ⟨[2,0], some ⟨-1,[0]⟩⟩ ⟨[0,2,2], some ⟨-2,[1]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,0], some ⟨-1,[0]⟩⟩ ⟨[0,2,2], some ⟨-2,[1]⟩⟩ = .lt := by decide
example : draftCmp [0,2,0,-2,0] [2,0,-2] = some .gt := by decide
example : fixedCmp ⟨[0,2,0], some ⟨-2,[0]⟩⟩ ⟨[2,0], some ⟨-2,[]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,2,0], some ⟨-2,[0]⟩⟩ ⟨[2,0], some ⟨-2,[]⟩⟩ = .gt := by decide
example : draftCmp [2,0,-1,0,1] [1,1,0,-1,1,1] = some .lt := by decide
example : fixedCmp ⟨[2,0], some ⟨-1,[0,1]⟩⟩ ⟨[1,1,0], some ⟨-1,[1,1]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,0], some ⟨-1,[0,1]⟩⟩ ⟨[1,1,0], some ⟨-1,[1,1]⟩⟩ = .lt := by decide
example : draftCmp [1,0,2,-2,0,1] [0,2,-2,1,1] = some .lt := by decide
example : fixedCmp ⟨[1,0,2], some ⟨-2,[0,1]⟩⟩ ⟨[0,2], some ⟨-2,[1,1]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,0,2], some ⟨-2,[0,1]⟩⟩ ⟨[0,2], some ⟨-2,[1,1]⟩⟩ = .lt := by decide
example : draftCmp [0,1,-3] [1,2,-2,1,1] = some .gt := by decide
example : fixedCmp ⟨[0,1], some ⟨-3,[]⟩⟩ ⟨[1,2], some ⟨-2,[1,1]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,1], some ⟨-3,[]⟩⟩ ⟨[1,2], some ⟨-2,[1,1]⟩⟩ = .gt := by decide
example : draftCmp [0,0,2,-1,1,1] [0,1,-3,0] = some .gt := by decide
example : fixedCmp ⟨[0,0,2], some ⟨-1,[1,1]⟩⟩ ⟨[0,1], some ⟨-3,[0]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,0,2], some ⟨-1,[1,1]⟩⟩ ⟨[0,1], some ⟨-3,[0]⟩⟩ = .gt := by decide
example : draftCmp [2,0,-3,1,1] [2,0,0,-2] = some .gt := by decide
example : fixedCmp ⟨[2,0], some ⟨-3,[1,1]⟩⟩ ⟨[2,0,0], some ⟨-2,[]⟩⟩ = .gt := by decide
example : refCmp ⟨[2,0], some ⟨-3,[1,1]⟩⟩ ⟨[2,0,0], some ⟨-2,[]⟩⟩ = .gt := by decide
example : draftCmp [1,0,1,-2,1,1] [0,0,1,-2,0,1] = some .lt := by decide
example : fixedCmp ⟨[1,0,1], some ⟨-2,[1,1]⟩⟩ ⟨[0,0,1], some ⟨-2,[0,1]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,0,1], some ⟨-2,[1,1]⟩⟩ ⟨[0,0,1], some ⟨-2,[0,1]⟩⟩ = .lt := by decide
example : draftCmp [0,2,1,-2,0] [1,0] = some .gt := by decide
example : fixedCmp ⟨[0,2,1], some ⟨-2,[0]⟩⟩ ⟨[1,0], none⟩ = .gt := by decide
example : refCmp ⟨[0,2,1], some ⟨-2,[0]⟩⟩ ⟨[1,0], none⟩ = .gt := by decide
example : draftCmp [1,0,-1,1,0] [1,1,1,-1,1] = some .gt := by decide
example : fixedCmp ⟨[1,0], some ⟨-1,[1,0]⟩⟩ ⟨[1,1,1], some ⟨-1,[1]⟩⟩ = .gt := by decide
example : refCmp ⟨[1,0], some ⟨-1,[1,0]⟩⟩ ⟨[1,1,1], some ⟨-1,[1]⟩⟩ = .gt := by decide
example : draftCmp [0,2,1,-3,0] [1,2,1] = some .gt := by decide
example : fixedCmp ⟨[0,2,1], some ⟨-3,[0]⟩⟩ ⟨[1,2,1], none⟩ = .gt := by decide
example : refCmp ⟨[0,2,1], some ⟨-3,[0]⟩⟩ ⟨[1,2,1], none⟩ = .gt := by decide
example : draftCmp [0,2,2,-3,0,1] [1,2,1,-3,1,0] = some .gt := by decide
example : fixedCmp ⟨[0,2,2], some ⟨-3,[0,1]⟩⟩ ⟨[1,2,1], some ⟨-3,[1,0]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,2,2], some ⟨-3,[0,1]⟩⟩ ⟨[1,2,1], some ⟨-3,[1,0]⟩⟩ = .gt := by decide
example : draftCmp [1,0,1,-1] [0,2,0,-3,0] = some .lt := by decide
example : fixedCmp ⟨[1,0,1], some ⟨-1,[]⟩⟩ ⟨[0,2,0], some ⟨-3,[0]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,0,1], some ⟨-1,[]⟩⟩ ⟨[0,2,0], some ⟨-3,[0]⟩⟩ = .lt := by decide
example : draftCmp [0,2,1,-2,1,1] [2,1,2,-1,0] = some .gt := by decide
example : fixedCmp ⟨[0,2,1], some ⟨-2,[1,1]⟩⟩ ⟨[2,1,2], some ⟨-1,[0]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,2,1], some ⟨-2,[1,1]⟩⟩ ⟨[2,1,2], some ⟨-1,[0]⟩⟩ = .gt := by decide
example : draftCmp [2,2,0,-1,1] [0,-3] = some .lt := by decide
example : fixedCmp ⟨[2,2,0], some ⟨-1,[1]⟩⟩ ⟨[0], some ⟨-3,[]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,2,0], some ⟨-1,[1]⟩⟩ ⟨[0], some ⟨-3,[]⟩⟩ = .lt := by decide
example : draftCmp [1,0,1,-3,0] [2,2,2,-2,0,0] = some .gt := by decide
example : fixedCmp ⟨[1,0,1], some ⟨-3,[0]⟩⟩ ⟨[2,2,2], some ⟨-2,[0,0]⟩⟩ = .gt := by decide
example : refCmp ⟨[1,0,1], some ⟨-3,[0]⟩⟩ ⟨[2,2,2], some ⟨-2,[0,0]⟩⟩ = .gt := by decide
example : draftCmp [1,2,0,-3,1] [2,1,2,-1,0] = some .gt := by decide
example : fixedCmp ⟨[1,2,0], some ⟨-3,[1]⟩⟩ ⟨[2,1,2], some ⟨-1,[0]⟩⟩ = .gt := by decide
example : refCmp ⟨[1,2,0], some ⟨-3,[1]⟩⟩ ⟨[2,1,2], some ⟨-1,[0]⟩⟩ = .gt := by decide
example : draftCmp [1,-3,0,1] [1,0,2,-3,1,0] = some .gt := by decide
example : fixedCmp ⟨[1], some ⟨-3,[0,1]⟩⟩ ⟨[1,0,2], some ⟨-3,[1,0]⟩⟩ = .gt := by decide
example : refCmp ⟨[1], some ⟨-3,[0,1]⟩⟩ ⟨[1,0,2], some ⟨-3,[1,0]⟩⟩ = .gt := by decide
example : draftCmp [1,2,0,-3] [1,2,2,-2,0,1] = some .gt := by decide
example : fixedCmp ⟨[1,2,0], some ⟨-3,[]⟩⟩ ⟨[1,2,2], some ⟨-2,[0,1]⟩⟩ = .gt := by decide
example : refCmp ⟨[1,2,0], some ⟨-3,[]⟩⟩ ⟨[1,2,2], some ⟨-2,[0,1]⟩⟩ = .gt := by decide
example : draftCmp [1,2,2,-1,1,1] [0,0,1,-1,1,1] = some .lt := by decide
example : fixedCmp ⟨[1,2,2], some ⟨-1,[1,1]⟩⟩ ⟨[0,0,1], some ⟨-1,[1,1]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,2,2], some ⟨-1,[1,1]⟩⟩ ⟨[0,0,1], some ⟨-1,[1,1]⟩⟩ = .lt := by decide
example : draftCmp [2,2,2,-3,1,0] [1,2,2,-2,0,0] = some .lt := by decide
example : fixedCmp ⟨[2,2,2], some ⟨-3,[1,0]⟩⟩ ⟨[1,2,2], some ⟨-2,[0,0]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,2,2], some ⟨-3,[1,0]⟩⟩ ⟨[1,2,2], some ⟨-2,[0,0]⟩⟩ = .lt := by decide
example : draftCmp [0,2,1,-2,1,1] [1,0,0,-3,0] = some .gt := by decide
example : fixedCmp ⟨[0,2,1], some ⟨-2,[1,1]⟩⟩ ⟨[1,0,0], some ⟨-3,[0]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,2,1], some ⟨-2,[1,1]⟩⟩ ⟨[1,0,0], some ⟨-3,[0]⟩⟩ = .gt := by decide
example : draftCmp [0,1,0,-1,1,0] [0,2,-3,0,1] = some .gt := by decide
example : fixedCmp ⟨[0,1,0], some ⟨-1,[1,0]⟩⟩ ⟨[0,2], some ⟨-3,[0,1]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,1,0], some ⟨-1,[1,0]⟩⟩ ⟨[0,2], some ⟨-3,[0,1]⟩⟩ = .gt := by decide
example : draftCmp [0,2,2,-2] [0,2,2,-2,0,0] = some .eq := by decide
example : fixedCmp ⟨[0,2,2], some ⟨-2,[]⟩⟩ ⟨[0,2,2], some ⟨-2,[0,0]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,2,2], some ⟨-2,[]⟩⟩ ⟨[0,2,2], some ⟨-2,[0,0]⟩⟩ = .gt := by decide
example : draftCmp [1,2,2,-3,0,0] [0,0,2,-1,1,0] = some .lt := by decide
example : fixedCmp ⟨[1,2,2], some ⟨-3,[0,0]⟩⟩ ⟨[0,0,2], some ⟨-1,[1,0]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,2,2], some ⟨-3,[0,0]⟩⟩ ⟨[0,0,2], some ⟨-1,[1,0]⟩⟩ = .lt := by decide
example : draftCmp [2,1,1,-1,1,0] [1,1,-3,0,0] = some .lt := by decide
example : fixedCmp ⟨[2,1,1], some ⟨-1,[1,0]⟩⟩ ⟨[1,1], some ⟨-3,[0,0]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,1,1], some ⟨-1,[1,0]⟩⟩ ⟨[1,1], some ⟨-3,[0,0]⟩⟩ = .lt := by decide
example : draftCmp [2,2,1,-2] [1,2,2,-2,0,1] = some .lt := by decide
example : fixedCmp ⟨[2,2,1], some ⟨-2,[]⟩⟩ ⟨[1,2,2], some ⟨-2,[0,1]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,2,1], some ⟨-2,[]⟩⟩ ⟨[1,2,2], some ⟨-2,[0,1]⟩⟩ = .lt := by decide
example : draftCmp [0,1,2,-1,0,0] [2,0,2,-2,1,0] = some .gt := by decide
example : fixedCmp ⟨[0,1,2], some ⟨-1,[0,0]⟩⟩ ⟨[2,0,2], some ⟨-2,[1,0]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,1,2], some ⟨-1,[0,0]⟩⟩ ⟨[2,0,2], some ⟨-2,[1,0]⟩⟩ = .gt := by decide
example : draftCmp [1,1,1] [2,1,2,-3,1,0] = some .gt := by decide
example : fixedCmp ⟨[1,1,1], none⟩ ⟨[2,1,2], some ⟨-3,[1,0]⟩⟩ = .gt := by decide
example : refCmp ⟨[1,1,1], none⟩ ⟨[2,1,2], some ⟨-3,[1,0]⟩⟩ = .gt := by decide
example : draftCmp [0,1,-1,1,0] [0,1,2,-2,0] = some .gt := by decide
example : fixedCmp ⟨[0,1], some ⟨-1,[1,0]⟩⟩ ⟨[0,1,2], some ⟨-2,[0]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,1], some ⟨-1,[1,0]⟩⟩ ⟨[0,1,2], some ⟨-2,[0]⟩⟩ = .gt := by decide
example : draftCmp [0,0,2,-3,0,0] [0,0,0,-1] = some .lt := by decide
example : fixedCmp ⟨[0,0,2], some ⟨-3,[0,0]⟩⟩ ⟨[0,0,0], some ⟨-1,[]⟩⟩ = .lt := by decide
example : refCmp ⟨[0,0,2], some ⟨-3,[0,0]⟩⟩ ⟨[0,0,0], some ⟨-1,[]⟩⟩ = .lt := by decide
example : draftCmp [0,2,2,-3,0] [1,0,0,-3,1,1] = some .gt := by decide
example : fixedCmp ⟨[0,2,2], some ⟨-3,[0]⟩⟩ ⟨[1,0,0], some ⟨-3,[1,1]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,2,2], some ⟨-3,[0]⟩⟩ ⟨[1,0,0], some ⟨-3,[1,1]⟩⟩ = .gt := by decide
example : draftCmp [0,2,2,-1,0,1] [2,2,0,-1,1] = some .gt := by decide
example : fixedCmp ⟨[0,2,2], some ⟨-1,[0,1]⟩⟩ ⟨[2,2,0], some ⟨-1,[1]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,2,2], some ⟨-1,[0,1]⟩⟩ ⟨[2,2,0], some ⟨-1,[1]⟩⟩ = .gt := by decide
example : draftCmp [1,2,0,-1,1,0] [0,2,2,-1,0,1] = some .lt := by decide
example : fixedCmp ⟨[1,2,0], some ⟨-1,[1,0]⟩⟩ ⟨[0,2,2], some ⟨-1,[0,1]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,2,0], some ⟨-1,[1,0]⟩⟩ ⟨[0,2,2], some ⟨-1,[0,1]⟩⟩ = .lt := by decide
example : draftCmp [0,0,0,-1,1,1] [1,2,2,-3,0] = some .gt := by decide
example : fixedCmp ⟨[0,0,0], some ⟨-1,[1,1]⟩⟩ ⟨[1,2,2], some ⟨-3,[0]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,0,0], some ⟨-1,[1,1]⟩⟩ ⟨[1,2,2], some ⟨-3,[0]⟩⟩ = .gt := by decide
example : draftCmp [2,0,2,-3] [0,2,2,-3] = some .lt := by decide
example : fixedCmp ⟨[2,0,2], some ⟨-3,[]⟩⟩ ⟨[0,2,2], some ⟨-3,[]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,0,2], some ⟨-3,[]⟩⟩ ⟨[0,2,2], some ⟨-3,[]⟩⟩ = .lt := by decide
example : draftCmp [1,0,2,-2,1,1] [0,0,1,-3,0] = some .lt := by decide
example : fixedCmp ⟨[1,0,2], some ⟨-2,[1,1]⟩⟩ ⟨[0,0,1], some ⟨-3,[0]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,0,2], some ⟨-2,[1,1]⟩⟩ ⟨[0,0,1], some ⟨-3,[0]⟩⟩ = .lt := by decide
example : draftCmp [1,1,-3,0,1] [0,-2,1] = some .lt := by decide
example : fixedCmp ⟨[1,1], some ⟨-3,[0,1]⟩⟩ ⟨[0], some ⟨-2,[1]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,1], some ⟨-3,[0,1]⟩⟩ ⟨[0], some ⟨-2,[1]⟩⟩ = .lt := by decide
example : draftCmp [2,0,1,-3] [0,2,2,-1] = some .lt := by decide
example : fixedCmp ⟨[2,0,1], some ⟨-3,[]⟩⟩ ⟨[0,2,2], some ⟨-1,[]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,0,1], some ⟨-3,[]⟩⟩ ⟨[0,2,2], some ⟨-1,[]⟩⟩ = .lt := by decide
example : draftCmp [2,1,-1,1,1] [1,2,1,-1,1,0] = some .lt := by decide
example : fixedCmp ⟨[2,1], some ⟨-1,[1,1]⟩⟩ ⟨[1,2,1], some ⟨-1,[1,0]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,1], some ⟨-1,[1,1]⟩⟩ ⟨[1,2,1], some ⟨-1,[1,0]⟩⟩ = .lt := by decide
example : draftCmp [1,0,1,-2,1,1] [0,0,0,-1,1,1] = some .lt := by decide
example : fixedCmp ⟨[1,0,1], some ⟨-2,[1,1]⟩⟩ ⟨[0,0,0], some ⟨-1,[1,1]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,0,1], some ⟨-2,[1,1]⟩⟩ ⟨[0,0,0], some ⟨-1,[1,1]⟩⟩ = .lt := by decide
example : draftCmp [0,1,0,-3,0,0] [0,1,0,-2,1,1] = some .gt := by decide
example : fixedCmp ⟨[0,1,0], some ⟨-3,[0,0]⟩⟩ ⟨[0,1,0], some ⟨-2,[1,1]⟩⟩ = .gt := by decide
example : refCmp ⟨[0,1,0], some ⟨-3,[0,0]⟩⟩ ⟨[0,1,0], some ⟨-2,[1,1]⟩⟩ = .gt := by decide
example : draftCmp [1,1] [0,0,0,-2,0,1] = some .lt := by decide
example : fixedCmp ⟨[1,1], none⟩ ⟨[0,0,0], some ⟨-2,[0,1]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,1], none⟩ ⟨[0,0,0], some ⟨-2,[0,1]⟩⟩ = .lt := by decide
example : draftCmp [1,0,2,-2,1,0] [1,0,1,-2] = some .lt := by decide
example : fixedCmp ⟨[1,0,2], some ⟨-2,[1,0]⟩⟩ ⟨[1,0,1], some ⟨-2,[]⟩⟩ = .lt := by decide
example : refCmp ⟨[1,0,2], some ⟨-2,[1,0]⟩⟩ ⟨[1,0,1], some ⟨-2,[]⟩⟩ = .lt := by decide
example : draftCmp [2,1,-3,1,0] [1,1,0,-2,0,0] = some .lt := by decide
example : fixedCmp ⟨[2,1], some ⟨-3,[1,0]⟩⟩ ⟨[1,1,0], some ⟨-2,[0,0]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,1], some ⟨-3,[1,0]⟩⟩ ⟨[1,1,0], some ⟨-2,[0,0]⟩⟩ = .lt := by decide
example : draftCmp [2,2,1,-1,1,1] [2,2,0,-2,1,0] = some .lt := by decide
example : fixedCmp ⟨[2,2,1], some ⟨-1,[1,1]⟩⟩ ⟨[2,2,0], some ⟨-2,[1,0]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,2,1], some ⟨-1,[1,1]⟩⟩ ⟨[2,2,0], some ⟨-2,[1,0]⟩⟩ = .lt := by decide
example : draftCmp [2,1,1,-3,1] [0,2,0,-3,1,0] = some .lt := by decide
example : fixedCmp ⟨[2,1,1], some ⟨-3,[1]⟩⟩ ⟨[0,2,0], some ⟨-3,[1,0]⟩⟩ = .lt := by decide
example : refCmp ⟨[2,1,1], some ⟨-3,[1]⟩⟩ ⟨[0,2,0], some ⟨-3,[1,0]⟩⟩ = .lt := by decide
example : draftCmp [1,1,2,-1] [2,1,1,-1,1,0] = some .gt := by decide
example : fixedCmp ⟨[1,1,2], some ⟨-1,[]⟩⟩ ⟨[2,1,1], some ⟨-1,[1,0]⟩⟩ = .gt := by decide
example : refCmp ⟨[1,1,2], some ⟨-1,[]⟩⟩ ⟨[2,1,1], some ⟨-1,[1,0]⟩⟩ = .gt := by decide
example : draftCmp [1,0,-1,1] [2,2,0,-1,1,0] = some .gt := by decide
example : fixedCmp ⟨[1,0], some ⟨-1,[1]⟩⟩ ⟨[2,2,0], some ⟨-1,[1,0]⟩⟩ = .gt := by decide
example : refCmp ⟨[1,0], some ⟨-1,[1]⟩⟩ ⟨[2,2,0], some ⟨-1,[1,0]⟩⟩ = .gt := by decide
