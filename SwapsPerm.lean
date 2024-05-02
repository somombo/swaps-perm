import Std.Data.Array.Lemmas

section subst_lemmas
section comm
-- @[simp]
private theorem fin_cast_val_comm (h1 : n = n' := by trivial) (h2 : n' = n'' := by trivial) (i : Fin n) : ((h1 ▸ h2 : n = n'') ▸ i : Fin n'')  =  (h2 ▸ (h1 ▸ i) : Fin n'') := by cases h1; rfl
-- @[simp]
private theorem prod_fin_cast_val_comm (h1 : n = n' := by trivial) (h2 : n' = n'' := by trivial) (p : Fin n × Fin n) : ((h1 ▸ h2 : n = n'') ▸ p : Fin n'' × Fin n'')  =  (h2 ▸ (h1 ▸ p) : Fin n'' × Fin n'') := by cases h1; rfl

-- @[simp]
private theorem list_prod_fin_cast_val_comm (h1 : n = n' := by trivial) (h2 : n' = n'' := by trivial) (ps: List (Fin n × Fin n)) : ((h1.symm ▸ h2 : n = n'') ▸ ps : List (Fin n'' × Fin n''))  =  (h2 ▸ (h1 ▸ ps) : List (Fin n'' × Fin n'')) := by cases h1; rfl

end comm

-- @[simp]
private theorem gen_cast_val_inverse {motive : Nat → Sort u} (h : n = n' := by trivial)  (x : motive n) : h.symm ▸ h ▸ x = x := by cases h; rfl

-- @[simp]
private theorem fin_cast_val (h : n = n' := by trivial) (i : Fin n) : h ▸ i = ⟨i.1, h ▸ i.2⟩ := by cases h; rfl
-- @[simp] private theorem Fin.cast_mk (h : n = m) (i : Nat) (hn : i < n) : Fin.cast h ⟨i, hn⟩ = ⟨i, h ▸ hn⟩ := rfl -- Already in Init.Data.Fin.Lemmas of Lean 4.7.0


-- @[simp]
private theorem prod_fin_cast_val (h : n = n' := by trivial) (p : Fin n × Fin n) : h ▸ p = (h ▸ p.1, h ▸ p.2) := by cases h; rfl


-- @[simp]
private theorem list_prod_fin_cast_val (h : n = n' := by trivial) (ps : List (Fin n × Fin n)) : h ▸ ps = ps.map (fun p => ⟨⟨p.1.1, h ▸ p.1.2⟩, ⟨p.2.1, h ▸ p.2.2⟩⟩) :=
  have aux : h ▸ ps = ps.map (h ▸ ·) := by cases h; simp -- ; apply Eq.symm; induction ps <;> simp_all
  by simp_all only [prod_fin_cast_val, fin_cast_val]

-- @[simp]
private theorem list_prod_fin_cast_val_append (h : n = n' := by trivial) (ps ps': List (Fin n × Fin n)) : h ▸ (ps ++ ps') =  (h ▸ ps) ++ (h ▸ ps') := by simp_all only [list_prod_fin_cast_val, List.map_append]


-- @[simp]
private theorem list_prod_fin_cast_val_reverse {ps : List (Fin n × Fin n)} (h : n = n' := by trivial) : h ▸ (ps.reverse) = (h ▸ ps).reverse := by cases h; rfl


end subst_lemmas


namespace Array

variable {a a': Array α} {i j p: Fin a.size}

@[simp] def swaps (a : Array α) : List (Fin a.size × Fin a.size) → Array α
  | [] => a
  | (i, j) :: ijs =>
    have : (a.swap i j).size = a.size := a.size_swap _ _

    -- swaps (a.swap i j) (this.symm ▸ ijs)
    swaps (a.swap i j) (ijs.map (fun p => ⟨⟨p.1.1, this.symm ▸ p.1.2⟩, ⟨p.2.1, this.symm ▸ p.2.2⟩⟩))
termination_by l => l.length



@[simp] theorem swaps_zero_eq_swap : a.swaps [] = a := by simp
@[simp] theorem swaps_one_eq_swap : a.swaps [(i, j)] = a.swap i j := by simp
-- @[simp] theorem swaps_two_eq_swap_swap {i1 j1 i2 j2 : Fin a.size}: a.swaps [(i1, j1),(i2, j2)] = (a.swap i1 j1).swap (a.size_swap _ _ ▸ i2) (a.size_swap _ _ ▸ j2) := by simp
-- @[simp] theorem swaps_two_eq_swap_swap' {i1 j1 i2 j2 : Fin a.size}: a.swaps [(i1, j1),(i2, j2)] = (a.swap i1 j1).swap (i2.cast (a.size_swap _ _).symm) (j2.cast (a.size_swap _ _).symm) :=  by simp
@[simp] theorem swaps_two_eq_swap_swap {i1 j1 i2 j2 : Fin a.size}: a.swaps [(i1, j1),(i2, j2)] = (a.swap i1 j1).swap (⟨i2.1, (a.size_swap _ _).symm ▸ i2.2⟩) ⟨j2.1, (a.size_swap _ _).symm ▸ j2.2⟩ :=  by simp

@[simp] theorem swaps_two_id : a.swaps [c,c]  = a := by let (i, j) := c; simp


@[simp] theorem size_swaps (a : Array α) : ∀ {l}, (a.swaps l).size = a.size
  | [] => by simp
  | (i, j) :: ijs => trans (size_swaps (a.swap i j) ..) (a.size_swap _ _)
termination_by l => l.length

set_option profiler true
set_option pp.proofs true
-- set_option pp.oneline true
set_option maxHeartbeats 5000000

#check toArrayLit


theorem swaps_congr {n : Nat} (a1 a2 : Array α) (l : List (Fin n × Fin n)) (ha1 : n = a1.size) (ha2 : n = a2.size) (heq : a1 = a2) : a1.swaps (ha1 ▸ l) = a2.swaps (ha2 ▸ l) := by
  have : {val := a1, property := ha1 : Subtype (n = ·.size)} = {val := a2, property := ha2: Subtype (n = ·.size)} := Subtype.eq heq
  apply congrArg (fun x => swaps x.1 (x.2 ▸ l)) this

-- {n : Nat} (a : Array α) (hsz : a.size = n) (h₂ : i < n)
-- have := h₁.symm ▸ h₂

-- attribute [simp] list_prod_fin_cast_val in -- required for termination proof
-- @[simp]
theorem swaps_append' {n : Nat} (a : Array α) (hsz : a.size = n) (l l': List (Fin n × Fin n)) : (a.swaps (hsz.symm ▸ l)).swaps ((Trans.trans hsz.symm a.size_swaps.symm) ▸ l') = a.swaps (hsz.symm ▸ (l ++ l')) := sorry




attribute [simp] list_prod_fin_cast_val in -- required for termination proof
@[simp] theorem swaps_append (a : Array α) (l l': List (Fin a.size × Fin a.size)) : (a.swaps l).swaps (a.size_swaps.symm ▸ l') = a.swaps (l ++ l') :=
  match l with
  | [] =>
    suffices (a.swaps []).swaps l' = a.swaps l' by simp_all only [List.nil_append]
    have : a.swaps [] = a :=  a.swaps_zero_eq_swap
    congrArg (fun _ => swaps a l') this

  | (i, j) :: ijs =>
    have hs : (a.swap i j).size = a.size := sorry -- a.size_swap _ _
    have hs's: ((a.swap i j).swaps (hs.symm ▸ ijs)).size = (a.swap i j).size := sorry -- (a.swap i j).size_swaps
    have hss : ((a.swap i j).swaps (hs.symm ▸ ijs)).size = a.size := sorry -- Trans.trans hs's hs

    have ih : ((a.swap i j).swaps (hs.symm ▸ ijs)).swaps (hs's.symm ▸ (hs.symm ▸ l')) = (a.swap i j).swaps ((hs.symm ▸ ijs) ++ (hs.symm ▸ l')) := sorry -- /- by apply -/ swaps_append (a.swap i j) (hs.symm ▸ ijs) (hs.symm ▸ l') -- FIXME: a bit slow

    have h_suff : ((a.swap i j).swaps (hs.symm ▸ ijs)).swaps (hss.symm ▸ l') = (a.swap i j).swaps (hs.symm ▸ (ijs ++ l')) :=
      sorry -- (list_prod_fin_cast_val_comm (hs.symm) (hs's.symm) (l')).symm ▸ ((list_prod_fin_cast_val_append hs.symm (ijs) (l')).symm ▸ ih) -- FIXME: slow


    have : (a.swaps ((i, j) :: ijs)).swaps (a.size_swaps.symm ▸ l') = ((a.swap i j).swaps (hs.symm ▸ ijs)).swaps (hss.symm ▸ l') := by apply swaps_congr ; simp only [swaps, list_prod_fin_cast_val]
    -- show (a.swaps ((i, j) :: ijs)).swaps (a.size_swaps.symm ▸ l') = a.swaps ((i, j) :: ijs ++ l') by
    sorry -- by simp_all only [list_prod_fin_cast_val, swaps, List.cons_append]
  -- termination_by l.length
  -- sorry

-- ih : ∀ (a : Array α) (hsz : a.size = n), a.swaps (hsz.symm ▸ (cs ++ cs.reverse)) = a
-- ih : (hsz : (a.swaps [c]).size = n)  →   (a.swaps [c]).swaps (hsz.symm ▸ (cs ++ cs.reverse)) = (a.swaps [c])


-- attribute [simp] list_prod_fin_cast_val in -- required for termination proof
-- -- @[simp]
-- -- set_option trace.profiler true in
theorem swaps_cancel' (n : Nat) (a : Array α) (hsz : a.size = n) (l : List (Fin n × Fin n)) : a.swaps (hsz.symm ▸ (l ++ l.reverse)) = a := by
  induction l generalizing a with
  | nil => simp only [List.reverse_nil, List.append_nil, list_prod_fin_cast_val, List.map_nil, swaps]
  | cons c cs ih => sorry




attribute [simp] list_prod_fin_cast_val in -- required for termination proof
-- @[simp]
-- set_option trace.profiler true in
theorem swaps_cancel (a : Array α) (l : List (Fin a.size × Fin a.size)) : a.swaps (l ++ l.reverse) = a :=
  match l with
  | [] => sorry -- by simp only [List.reverse_nil, List.append_nil, swaps]

  | c :: cs =>

    have hs' : (a.swaps [c]).size = a.size := sorry -- by rw [size_swaps] -- a.size_swaps

    have hs'' : ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).size = (a.swaps [c]).size := sorry -- by rw [size_swaps] -- (a.swaps [c]).size_swaps
    have hs : ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).size = a.size :=  sorry -- by simp only [size_swaps] -- hs''.symm ▸ hs'

    have : ((a.swaps [c]).swaps ((hs'.symm ▸ cs) ++ (hs'.symm ▸ cs).reverse)) = (a.swaps [c]) := sorry -- by /- show_term -/ apply swaps_cancel -- swaps_cancel (a.swaps [c]) (hs'.symm ▸ cs)
    -- have : ((a.swaps [c]).swaps ((hs'.symm ▸ cs) ++ (hs'.symm ▸ cs).reverse)) = (a.swaps [c]) := by  /- with_reducible -/ exact (swaps_cancel (a.swaps [c]) (hs'.symm ▸ cs))
    -- have : ((a.swaps [c]).swaps ((hs'.symm ▸ cs) ++ (hs'.symm ▸ cs).reverse)) = (a.swaps [c]) := (swaps_cancel (a.swaps [c]) (hs'.symm ▸ cs))


    have : ((a.swaps [c]).swaps ((hs'.symm ▸ cs) ++ (hs'.symm ▸ cs.reverse))) = (a.swaps [c]) := sorry -- by rw [(list_prod_fin_cast_val_reverse hs'.symm)]; exact this -- (list_prod_fin_cast_val_reverse hs'.symm) ▸ this


    have ih : ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))) = (a.swaps [c]) := sorry -- by rw [(list_prod_fin_cast_val_append hs'.symm ..)]; exact this -- (list_prod_fin_cast_val_append hs'.symm .. ▸ this)

    calc  a.swaps ((c :: cs) ++ (c :: cs).reverse)
      _ = a.swaps (      [c] ++ (cs ++ cs.reverse ++ [c])     ) := sorry -- by simp only [List.reverse_cons, List.cons_append, List.append_assoc, List.nil_append]
      _ = (a.swaps [c]).swaps ( hs'.symm ▸ (cs ++ cs.reverse ++ [c]) ) := sorry -- by apply Eq.symm ; apply swaps_append -- (swaps_append a [c] (cs ++ cs.reverse ++ [c])).symm
      _ = (a.swaps [c]).swaps ( (hs'.symm ▸ (cs ++ cs.reverse)) ++ (hs'.symm ▸ [c]) ) := sorry -- by simp only [list_prod_fin_cast_val, List.map_append]
      _ = ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).swaps  (hs''.symm ▸ (hs'.symm ▸ [c])) := sorry -- by apply Eq.symm ; apply swaps_append -- (swaps_append (a.swaps [c])  (hs'.symm ▸ (cs ++ cs.reverse)) (hs'.symm ▸ [c])).symm
      _ = ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).swaps  (hs.symm ▸ [c]) := sorry -- by simp only [list_prod_fin_cast_val, List.map] -- by rw [(list_prod_fin_cast_val_comm hs'.symm hs''.symm [c])]-- xx
      _ = (a.swaps [c]).swaps  (hs'.symm ▸ [c]) := swaps_congr ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))) (a.swaps [c]) [c] (hs.symm) (hs'.symm) ih
      _ = a.swaps ([c] ++ [c]) := sorry -- by apply swaps_append -- swaps_append a [c] [c]
      _ = a := sorry -- swaps_two_id
    -- sorry

  -- termination_by l.length
  -- sorry
