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

private theorem list_prod_fin_cast_val_reverse {ps : List (Fin n × Fin n)} (h : n = n') : h ▸ (ps.reverse) = (h ▸ ps).reverse := by cases h; rfl

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

@[simp] theorem swaps_zero_eq_swap : a.swaps [] = a := by simp [swaps]
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


-- set_option trace.profiler true in
attribute [simp] list_prod_fin_cast_val in -- required for termination proof
theorem swaps_append (a : Array α) (l l': List (Fin a.size × Fin a.size)) : (a.swaps l).swaps (a.size_swaps.symm ▸ l') = a.swaps (l ++ l') :=
  match l with
  | [] => by
    have : a.swaps [] = a :=  a.swaps_zero_eq_swap
    have : (a.swaps []).swaps l' = a.swaps l' := congrArg (fun _ => swaps a l') this
    simp_all only [List.nil_append]
  | (i, j) :: ijs =>
    have hs : (a.swap i j).size = a.size := a.size_swap _ _
    have hs's: ((a.swap i j).swaps (hs.symm ▸ ijs)).size = (a.swap i j).size := (a.swap i j).size_swaps
    have hss : ((a.swap i j).swaps (hs.symm ▸ ijs)).size = a.size := Trans.trans hs's hs

    have ih : ((a.swap i j).swaps (hs.symm ▸ ijs)).swaps (hs's.symm ▸ (hs.symm ▸ l')) = (a.swap i j).swaps ((hs.symm ▸ ijs) ++ (hs.symm ▸ l')) := by apply swaps_append (a.swap i j) (hs.symm ▸ ijs) (hs.symm ▸ l') -- TODO: using apply tactic to speed it up. But shouldnt otherwise be necessary

    have h_suff : ((a.swap i j).swaps (hs.symm ▸ ijs)).swaps (hss.symm ▸ l') = (a.swap i j).swaps (hs.symm ▸ (ijs ++ l')) :=
      (list_prod_fin_cast_val_comm (hs.symm) (hs's.symm) (l')).symm
      ▸ (list_prod_fin_cast_val_append hs.symm (ijs) (l')).symm
      ▸ ih

    have : (a.swaps ((i, j) :: ijs)).swaps (a.size_swaps.symm ▸ l') = ((a.swap i j).swaps (hs.symm ▸ ijs)).swaps (hss.symm ▸ l') := by apply swaps_congr ; simp only [swaps, list_prod_fin_cast_val]

    by simp_all only [list_prod_fin_cast_val, swaps, List.cons_append]
  termination_by l.length

set_option maxHeartbeats 5000000 in
attribute [simp] list_prod_fin_cast_val in -- required for termination proof
theorem swaps_cancel (a : Array α) (l : List (Fin a.size × Fin a.size)) : a.swaps (l ++ l.reverse) = a :=
  match l with
  | [] => by simp only [List.reverse_nil, List.append_nil, swaps]

  | c :: cs =>

    have hs' : (a.swaps [c]).size = a.size := by rw [size_swaps] -- a.size_swaps

    have hs'' : ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).size = (a.swaps [c]).size := by rw [size_swaps] -- (a.swaps [c]).size_swaps
    have hs : ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).size = a.size :=  by simp only [size_swaps] -- hs''.symm ▸ hs'

    have : ((a.swaps [c]).swaps ((hs'.symm ▸ cs) ++ (hs'.symm ▸ cs).reverse)) = (a.swaps [c]) := swaps_cancel (a.swaps [c]) (hs'.symm ▸ cs)
    -- have : ((a.swaps [c]).swaps ((hs'.symm ▸ cs) ++ (hs'.symm ▸ cs).reverse)) = (a.swaps [c]) := by exact (swaps_cancel (a.swaps [c]) (hs'.symm ▸ cs))
    -- have : ((a.swaps [c]).swaps ((hs'.symm ▸ cs) ++ (hs'.symm ▸ cs).reverse)) = (a.swaps [c]) := by /- show_term -/ apply swaps_cancel
    -- have : ((a.swaps [c]).swaps ((hs'.symm ▸ cs) ++ (hs'.symm ▸ cs).reverse)) = (a.swaps [c]) := by  /- with_reducible -/ exact (swaps_cancel (a.swaps [c]) (hs'.symm ▸ cs))

    have : ((a.swaps [c]).swaps ((hs'.symm ▸ cs) ++ (hs'.symm ▸ cs.reverse))) = (a.swaps [c]) := by rw [(list_prod_fin_cast_val_reverse hs'.symm)]; exact this -- (list_prod_fin_cast_val_reverse hs'.symm) ▸ this
    have ih : ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))) = (a.swaps [c]) := by rw [(list_prod_fin_cast_val_append hs'.symm ..)]; exact this -- (list_prod_fin_cast_val_append hs'.symm .. ▸ this)

    calc  a.swaps ((c :: cs) ++ (c :: cs).reverse)
      _ = a.swaps (      [c] ++ (cs ++ cs.reverse ++ [c])     ) := by simp only [List.reverse_cons, List.cons_append, List.append_assoc, List.nil_append]
      _ = (a.swaps [c]).swaps ( hs'.symm ▸ (cs ++ cs.reverse ++ [c]) ) := by apply Eq.symm ; apply swaps_append -- (swaps_append a [c] (cs ++ cs.reverse ++ [c])).symm
      _ = (a.swaps [c]).swaps ( (hs'.symm ▸ (cs ++ cs.reverse)) ++ (hs'.symm ▸ [c]) ) := by simp only [list_prod_fin_cast_val, List.map_append]
      _ = ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).swaps  (hs''.symm ▸ hs'.symm ▸ [c]) := by apply Eq.symm ; apply swaps_append -- (swaps_append (a.swaps [c])  (hs'.symm ▸ (cs ++ cs.reverse)) (hs'.symm ▸ [c])).symm

      -- _ = ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).swaps  (hs.symm ▸ [c]) := by simp only [list_prod_fin_cast_val, List.map] -- FIXME: is slow appox. 6seconds
      _ = ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).swaps  (hs.symm ▸ [c]) := /- show_term by rw [(list_prod_fin_cast_val_comm hs'.symm hs''.symm [c])] --> FIXME: is slow appox. 9seconds -/ Eq.mpr (id (congrArg (fun _a => swaps (swaps (swaps a [c]) (Eq.symm hs' ▸ (cs ++ List.reverse cs))) (Eq.symm hs'' ▸ Eq.symm hs' ▸ [c]) = swaps (swaps (swaps a [c]) (Eq.symm hs' ▸ (cs ++ List.reverse cs))) _a) (list_prod_fin_cast_val_comm (Eq.symm hs') (Eq.symm hs'') [c]))) (Eq.refl (swaps (swaps (swaps a [c]) (Eq.symm hs' ▸ (cs ++ List.reverse cs))) (Eq.symm hs'' ▸ Eq.symm hs' ▸ [c])))-- FIXME: is appox. 3.5seconds

      _ = (a.swaps [c]).swaps  (hs'.symm ▸ [c]) := swaps_congr ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))) (a.swaps [c]) [c] (hs.symm) (hs'.symm) ih
      _ = a.swaps ([c] ++ [c]) := by apply swaps_append -- swaps_append a [c] [c]
      _ = a := swaps_two_id

  termination_by l.length


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
      _ = a1.swaps (l ++ l.reverse) := swaps_append a1 l l.reverse
      _ = a1 := swaps_cancel a1 l

  ⟨(h.symm ▸ a1.size_swaps) ▸ l.reverse, this.symm⟩


theorem trans (h1 : a1 ~ a2) (h2 : a2 ~ a3) : a1 ~ a3 :=

  let ⟨l1, h1'⟩ := h1; -- have h1' : a2 = a1.swaps l1 := h1'
  let ⟨l2, h2'⟩ := h2; -- have h2' : a3 = a2.swaps l2 := h2'

  have hs1 : a1.size = (a1.swaps l1).size := (a1.size_swaps).symm
  have hs2 : a2.size = a1.size := h1'.symm ▸ a1.size_swaps
  have hs3 : a2.size = (a1.swaps l1).size := Trans.trans hs2 hs1

  have h3' : a3 = (a1.swaps l1).swaps ((Trans.trans hs2 hs1) ▸ l2) := h1' ▸ h2'

  have : (a1.swaps l1).swaps (hs3 ▸ l2) = a1.swaps (l1 ++ (hs2 ▸ l2)) := calc _
    _ = (a1.swaps l1).swaps (a1.size_swaps.symm ▸ hs2 ▸ l2) := by simp only [←list_prod_fin_cast_val_comm]
    _ = a1.swaps (l1 ++ (hs2 ▸ l2)) := a1.swaps_append l1 (hs2 ▸ l2)

  have : a3 = a1.swaps (l1 ++ (hs2 ▸ l2)) := Trans.trans h3'  this

  ⟨l1 ++ (hs2 ▸ l2), this⟩



instance : Trans (. ~ . : Array α → Array α → Prop) (. ~ . : Array α → Array α → Prop) (. ~ . : Array α → Array α → Prop) where
  trans := Array.Perm.trans

theorem equivalence (α) : Equivalence (@Perm α) := ⟨Perm.refl, Perm.symm, Perm.trans⟩
instance isSetoid (α) : Setoid (Array α) := ⟨(@Perm α), (Perm.equivalence α)⟩


end Perm
