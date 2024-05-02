def Array.swaps (a : Array α) : List (Fin a.size × Fin a.size) → Array α
  | [] => a
  | (i, j) :: ijs =>
    have : (a.swap i j).size = a.size := a.size_swap _ _

    swaps (a.swap i j) (ijs.map (fun p => ⟨⟨p.1.1, this.symm ▸ p.1.2⟩, ⟨p.2.1, this.symm ▸ p.2.2⟩⟩))
termination_by l => l.length

set_option trace.profiler true in
theorem Array.swaps_cancel (a : Array α) (l : List (Fin a.size × Fin a.size)) : a.swaps (l ++ l.reverse) = a :=
  match l with
  | [] => sorry
  | c :: cs =>

    have h : a.size = (a.swaps [c]).size := sorry

    have ih1 : ((a.swaps [c]).swaps ((h ▸ cs) ++ (h ▸ cs).reverse)) = (a.swaps [c]) := swaps_cancel (a.swaps [c]) (h ▸ cs) -- FIXME: takes approx 5s
    -- have ih2 : swaps (swaps a [c]) (h ▸ cs ++ List.reverse (h ▸ cs)) = swaps a [c] := swaps_cancel (a.swaps [c]) (h ▸ cs) -- FIXME: takes approx 1.7s
    -- have ih3 : ((a.swaps [c]).swaps ((h ▸ cs) ++ (h ▸ cs).reverse)) = (a.swaps [c])  := by exact swaps_cancel (a.swaps [c]) (h ▸ cs) -- LGTM: takes approx 0.025s
    -- have ih4  := swaps_cancel (a.swaps [c]) (h ▸ cs) -- LGTM: takes approx 0.018s

    sorry
termination_by l.length
decreasing_by sorry
