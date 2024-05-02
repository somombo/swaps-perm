/-
  Copyright 2024 Chisomo Makombo Sakala
  Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
  in compliance with the License. You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
  Unless required by applicable law or agreed to in writing, software distributed under the License
  is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
  or implied. See the License for the specific language governing permissions and limitations under
  the License.
-/

import Std.Data.Array.Lemmas

section subst_lemmas

private theorem list_prod_fin_cast_val_comm (h1 : n = n') (h2 : n' = n'') (ps: List (Fin n × Fin n)) : ((h1.symm ▸ h2 : n = n'') ▸ ps : List (Fin n'' × Fin n''))  =  (h2 ▸ (h1 ▸ ps) : List (Fin n'' × Fin n'')) := by cases h1; rfl

private theorem fin_cast_val (h : n = n') (i : Fin n) : h ▸ i = ⟨i.1, h ▸ i.2⟩ := by cases h; rfl

private theorem prod_fin_cast_val (h : n = n') (p : Fin n × Fin n) : h ▸ p = (h ▸ p.1, h ▸ p.2) := by cases h; rfl

private theorem list_prod_fin_cast_val (h : n = n') (ps : List (Fin n × Fin n)) : h ▸ ps = ps.map (fun p => ⟨⟨p.1.1, h ▸ p.1.2⟩, ⟨p.2.1, h ▸ p.2.2⟩⟩) :=
  have aux : h ▸ ps = ps.map (h ▸ ·) := by cases h; simp -- ; apply Eq.symm; induction ps <;> simp_all
  by simp_all only [prod_fin_cast_val, fin_cast_val]

private theorem list_prod_fin_cast_val_append (h : n = n') (ps ps': List (Fin n × Fin n)) : h ▸ (ps ++ ps') =  (h ▸ ps) ++ (h ▸ ps') := by simp_all only [list_prod_fin_cast_val, List.map_append]

end subst_lemmas


namespace Array

variable {a a': Array α} {i j p: Fin a.size}

def swaps (a : Array α) : List (Fin a.size × Fin a.size) → Array α
  | [] => a
  | (i, j) :: ijs =>
    have : (a.swap i j).size = a.size := a.size_swap _ _

    -- swaps (a.swap i j) (this.symm ▸ ijs)
    swaps (a.swap i j) (ijs.map (fun p => ⟨⟨p.1.1, this.symm ▸ p.1.2⟩, ⟨p.2.1, this.symm ▸ p.2.2⟩⟩))
termination_by l => l.length

@[simp] theorem swaps_nil : a.swaps [] = a := by simp [swaps]
theorem swaps_cons : a.swaps ((i, j) :: ijs) = (a.swap i j).swaps ((a.size_swap ..).symm ▸ ijs) := by simp only [swaps, list_prod_fin_cast_val]

@[simp] theorem swaps_one_eq_swap : a.swaps [(i, j)] = a.swap i j := by simp [swaps]
@[simp] theorem swaps_two_eq_swap_swap {i1 j1 i2 j2 : Fin a.size}: a.swaps [(i1, j1),(i2, j2)] = (a.swap i1 j1).swap (⟨i2.1, (a.size_swap _ _).symm ▸ i2.2⟩) ⟨j2.1, (a.size_swap _ _).symm ▸ j2.2⟩ :=  by simp [swaps]

@[simp] theorem swaps_two_id : a.swaps [c,c]  = a := by let (i, j) := c; simp

theorem swaps_congr {n : Nat} (a1 a2 : Array α) (l : List (Fin n × Fin n)) (ha1 : n = a1.size) (ha2 : n = a2.size) (heq : a1 = a2) : a1.swaps (ha1 ▸ l) = a2.swaps (ha2 ▸ l) := by
  have : {val := a1, property := ha1 : Subtype (n = ·.size)} = {val := a2, property := ha2: Subtype (n = ·.size)} := Subtype.eq heq
  apply congrArg (fun x => swaps x.1 (x.2 ▸ l)) this

@[simp] theorem size_swaps (a : Array α) : ∀ {l}, (a.swaps l).size = a.size
  | [] => by simp
  | (i, j) :: ijs => trans (size_swaps (a.swap i j) ..) (a.size_swap _ _)
termination_by l => l.length

theorem swaps_append_lit  {n n' : Nat} (a : Array α) (l : List (Fin n × Fin n)) (l' : List (Fin n' × Fin n')) (hn : n = a.size) (h : n' = n) (hn' : n' = (a.swaps (hn ▸ l)).size) : (a.swaps (hn ▸ l)).swaps (hn' ▸ l') = a.swaps ((hn ▸ l) ++ ((Trans.trans h hn) ▸ l')) := by
  have hs_0 : n' = a.size := Trans.trans h hn
  induction l generalizing a with
  | nil =>
    have : a.swaps (hn ▸ []) = a :=  by simp only [list_prod_fin_cast_val, List.map_nil, swaps]
    have : (a.swaps (hn ▸ [])).swaps (hn' ▸ l') = a.swaps (hs_0 ▸ l') := by apply swaps_congr ; exact this
    simp_all only [list_prod_fin_cast_val, List.map_nil, List.nil_append]
  | cons c ijs ih => cases c with | mk i j =>

    have hs : (a.swap (hn ▸ i) (hn ▸ j)).size = a.size := a.size_swap ..
    have hn_1 : n = (a.swap (hn ▸ i) (hn ▸ j)).size := Trans.trans hn hs.symm
    have hs's: ((a.swap (hn ▸ i) (hn ▸ j)).swaps (hn_1 ▸ ijs)).size = (a.swap (hn ▸ i) (hn ▸ j)).size := by simp only [size_swaps]
    have hss : ((a.swap (hn ▸ i) (hn ▸ j)).swaps (hn_1 ▸ ijs)).size = a.size := Trans.trans hs's hs
    have hn'_ : n' = ((a.swap (hn ▸ i) (hn ▸ j)).swaps (hn_1 ▸ ijs)).size := Trans.trans hs_0 hss.symm
    have hn''__ : n' = (a.swap (hn ▸ i) (hn ▸ j)).size := Trans.trans h hn_1

    have : a.swaps (hn ▸ ((i, j) :: ijs)) = (a.swap (hn ▸ i) (hn ▸ j)).swaps (hn_1 ▸ ijs) := calc _
      _ = a.swaps (((hn ▸ i, hn ▸ j) :: (hn ▸ ijs))) := by simp only [list_prod_fin_cast_val, List.map_cons, fin_cast_val]
      _ = (a.swap (hn ▸ i) (hn ▸ j)).swaps (hn_1 ▸ ijs) := by simp only [swaps_cons, ←list_prod_fin_cast_val_comm]

    calc (a.swaps (hn ▸ ((i, j) :: ijs))).swaps (hn' ▸ l')
      _ = ((a.swap (hn ▸ i) (hn ▸ j)).swaps (hn_1 ▸ ijs)).swaps (hn'_ ▸ l') := by apply swaps_congr ; assumption
      _ = (a.swap (hn ▸ i) (hn ▸ j)).swaps ((hn_1 ▸ ijs) ++ (hn''__ ▸ l')) := by apply ih (a.swap (hn ▸ i) (hn ▸ j)) ; assumption
      _ = (a.swap (hn ▸ i) (hn ▸ j)).swaps (hs.symm ▸ ((hn ▸ ijs) ++ (hs_0 ▸ l'))) := by congr ; simp only [list_prod_fin_cast_val_append, ←list_prod_fin_cast_val_comm]
      _ = a.swaps ((hn ▸ i, hn ▸ j) :: ((hn ▸ ijs) ++ (hs_0 ▸ l'))) :=  by simp only [swaps_cons]
      _ = a.swaps ((hn ▸ ((i, j) :: ijs)) ++ (hs_0 ▸ l')) := by simp only [fin_cast_val, list_prod_fin_cast_val, List.map_cons, List.cons_append]


theorem swaps_cancel_lit {a_size : Nat} (a : Array α) (l : List (Fin a_size × Fin a_size)) (h : a.size = a_size := by rfl) : a.swaps (h.symm ▸ (l ++ l.reverse)) = a := by
  induction l generalizing a with
  | nil => simp only [List.reverse_nil, List.append_nil, list_prod_fin_cast_val, List.map_nil, swaps]
  | cons c cs ih =>

    have hs' : (a.swaps (h.symm ▸ [c])).size = a_size := trans a.size_swaps h
    have hs'' : ((a.swaps (h.symm ▸ [c])).swaps (hs'.symm ▸ (cs ++ cs.reverse))).size = (a.swaps (h.symm ▸ [c])).size := by rw [size_swaps]
    have hs : ((a.swaps (h.symm ▸ [c])).swaps (hs'.symm ▸ (cs ++ cs.reverse))).size = a_size :=  trans hs'' hs'

    have ih : (a.swaps (h.symm ▸ [c])).swaps (hs'.symm ▸ (cs ++ cs.reverse)) = a.swaps (h.symm ▸ [c]) := ih (a.swaps (h.symm ▸[c])) hs'

    calc a.swaps (h.symm ▸ ((c :: cs) ++ (c :: cs).reverse))
      _ = a.swaps (h.symm ▸ ([c] ++ (cs ++ cs.reverse ++ [c]))) := by simp only [List.reverse_cons, List.cons_append, List.append_assoc, List.nil_append]
      _ = a.swaps ((h.symm ▸ [c]) ++ (h.symm ▸ (cs ++ cs.reverse ++ [c]))) := by simp only [list_prod_fin_cast_val, List.map_append]
      _ = (a.swaps (h.symm ▸ [c])).swaps (hs'.symm ▸ (cs ++ cs.reverse ++ [c])) := by apply Eq.symm ; apply swaps_append_lit ; rfl
      _ = (a.swaps (h.symm ▸ [c])).swaps ((hs'.symm ▸ (cs ++ cs.reverse)) ++ (hs'.symm ▸ [c])) := by simp only [list_prod_fin_cast_val, List.map_append]
      _ = ((a.swaps (h.symm ▸ [c])).swaps (hs'.symm ▸ (cs ++ cs.reverse))).swaps  (hs''.symm ▸ hs'.symm ▸ [c]) := by apply Eq.symm ; apply swaps_append_lit ; exact hs'
      _ = ((a.swaps (h.symm ▸ [c])).swaps (hs'.symm ▸ (cs ++ cs.reverse))).swaps  (hs.symm ▸ [c]) := by simp only [list_prod_fin_cast_val, List.map] -- by rw [(list_prod_fin_cast_val_comm hs'.symm hs''.symm [c])] -- FIXME: is a bit slow appox. 2-3seconds
      _ = (a.swaps (h.symm ▸ [c])).swaps  (hs'.symm ▸ [c]) := swaps_congr ((a.swaps (h.symm ▸ [c])).swaps (hs'.symm ▸ (cs ++ cs.reverse))) (a.swaps (h.symm ▸ [c])) [c] (hs.symm) (hs'.symm) ih -- by apply swaps_congr ; exact ih
      _ = a.swaps ((h.symm ▸ [c]) ++ (h.symm ▸ [c])) := by apply swaps_append_lit ; rfl
      _ = a.swaps (h.symm ▸ ([c] ++ [c])) := by simp only [list_prod_fin_cast_val, List.map_append]
      _ = a := by simp only [List.singleton_append, list_prod_fin_cast_val, List.map_cons, List.map_nil, swaps_two_id]


@[simp] def Perm (a a' : Array α) := ∃ (l : List (Fin a.size × Fin a.size)), a' = a.swaps l

/-
  Defines notation for "a 'is a permutation of' b".
  FIXME: `(priority := high)` is currently set in order to (potentially) override
  incompatible definition found in Mathlib.Data.List.Perm
  The ideal solution would be for the ~ symbol to be defined by a type class
  that can accommodate different variations of the definition of permutation
  (e.g. as a bijection)
-/
infixl:50 (priority := high) " ~ " => Perm

namespace Perm
variable {a1 a2 a3 : Array α}

theorem size_eq (h : a1 ~ a2) : a1.size = a2.size := by cases h ; simp_all

theorem refl : ∀ a : Array α, a ~ a := fun _ => ⟨[], by simp⟩
theorem of_eq (h : a1 = a2) : a1 ~ a2 := h ▸ refl a1


theorem symm (h : a1 ~ a2) : a2 ~ a1 :=
  let ⟨l, h⟩ := h; -- have h : a2 = (a1.swaps l) := h

  have : a2.swaps ((h.symm ▸ a1.size_swaps) ▸ l.reverse) = a1 := calc
      _ = (a1.swaps l).swaps (a1.size_swaps ▸ l.reverse) := by apply swaps_congr ; assumption
      _ = a1.swaps (l ++ l.reverse) := by apply swaps_append_lit a1 l l.reverse <;> rfl
      _ = a1 := by apply swaps_cancel_lit a1 l

  ⟨(h.symm ▸ a1.size_swaps) ▸ l.reverse, this.symm⟩


theorem trans (h1 : a1 ~ a2) (h2 : a2 ~ a3) : a1 ~ a3 :=

  let ⟨l1, h1'⟩ := h1; -- have h1' : a2 = a1.swaps l1 := h1'
  let ⟨l2, h2'⟩ := h2; -- have h2' : a3 = a2.swaps l2 := h2'

  have hs1 : a1.size = (a1.swaps l1).size := (a1.size_swaps).symm
  have hs2 : a2.size = a1.size := h1'.symm ▸ a1.size_swaps
  have hs3 : a2.size = (a1.swaps l1).size := Trans.trans hs2 hs1

  have h3' : a3 = (a1.swaps l1).swaps ((Trans.trans hs2 hs1) ▸ l2) := h1' ▸ h2'
  have : (a1.swaps l1).swaps (hs3 ▸ l2) = a1.swaps (l1 ++ (hs2 ▸ l2)) := swaps_append_lit a1 l1 l2 rfl hs2 hs3

  have : a3 = a1.swaps (l1 ++ (hs2 ▸ l2)) := Trans.trans h3' this

  ⟨l1 ++ (hs2 ▸ l2), this⟩



instance : Trans (. ~ . : Array α → Array α → Prop) (. ~ . : Array α → Array α → Prop) (. ~ . : Array α → Array α → Prop) where
  trans := Array.Perm.trans

theorem equivalence (α) : Equivalence (@Perm α) := ⟨Perm.refl, Perm.symm, Perm.trans⟩
instance isSetoid (α) : Setoid (Array α) := ⟨(@Perm α), (Perm.equivalence α)⟩


end Perm