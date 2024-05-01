import SwapsPerm

def as := #[2, 3, 1]

instance : OfNat (Fin as.size) i := ⟨Fin.ofNat i⟩
-- ^^allows conversion of Nat index to (Fin as.size) by modding (%) by as.size

def as1 := as.swap 0 2
#eval as1 -- result : #[1, 3, 2]

instance : OfNat (Fin as1.size) i := ⟨Fin.ofNat i⟩
-- ^^allows conversion of Nat index to (Fin as1.size) by modding (%) by as1.size

def as2 := as1.swap 1 2
#eval as2 -- result : #[1, 2, 3]

--- The above is the same as just doing:
#eval as.swaps [(0, 2), (1, 2)] -- result : #[1, 2, 3]

-- The "is a permutation of" relation `Array.Perm` denoted `~` is defined by SwapsPerm library
-- The following proves that #[2, 3, 1] is a permutation of #[1, 2, 3]:
example : as ~ #[1, 2, 3] := Exists.intro [(0, 2), (1, 2)] (by simp_arith)
