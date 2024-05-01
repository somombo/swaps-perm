# swaps-perm

This project formally defines two arrays to be *permutations* of one another if one can be expressed as a sequence of "swaps" (also known as 2-cycles or transpositions)[^1] of the other. Beyond establishing other related theorems, we provide a formal proof that such a binary relation is in fact an equivalence relation. 

In general, any permutation can be expressed as a "product" (composition) of 2-cycles[^2]. Therefore, any permutation of an array can always be derived from a sequence of swaps which we are able to perform all at once (as shown in the example below).

This project serves as a foundation for further exploration of array-permutation related concepts and algorithms within Lean 4.

## Usage

First add `require «swaps-perm» from git "https://github.com/somombo/swaps-perm.git" @ "main"` to your `lakefile.lean`. Here is an [example](/Example.lean) of how to use it:

```lean
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
```

[^1]: Cyclic permutation - Transpositions, https://en.wikipedia.org/w/index.php?title=Cyclic_permutation&oldid=1219665352#Transpositions (last visited May 2, 2024).
[^2]: Permutation is Product of Transpositions, https://proofwiki.org/wiki/Permutation_is_Product_of_Transpositions.