/-!
# No finite magma refutes 1167 implies 1763

Law 1167 is `x = y ◇ ((z ◇ (y ◇ y)) ◇ x)`, law 1763 is `x = (y ◇ z) ◇ ((x ◇ z) ◇ x)`.

Every model of 1167 has involutive left translations and an injective squaring map, with no
finiteness assumption. If squaring is also surjective, 1763 holds. On `Fin n` an injective
self-map is surjective, so no finite countermodel exists on any carrier size.

The natural-number model in the hard2_0027 certificate of the solver by Ma, Zhang and Cázares, which
is the ETP's `op_1659_4315`, is exactly the escape: there
`y ◇ y = y + 1`, which is injective and misses 0, and 1763 can only fail at `z = 0`.

The finite statement is already in the ETP as `Eq1133.Finite.Equation1167_implies_Equation1096`
plus three general implications. This route is direct and needs no Mathlib.

Core Lean only. Every theorem closes over no axioms, `propext` included.

Copyright 2026 Carlo Perassi. SPDX-License-Identifier: Apache-2.0
Written with Claude Code (Claude Opus 5.5), for Carlo Perassi.
-/

class Magma (α : Type) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

namespace Law1167

variable {G : Type} [Magma G] (h : ∀ x y z : G, x = y ◇ ((z ◇ (y ◇ y)) ◇ x))
include h

theorem left_invol_aux (a z t : G) : (z ◇ (a ◇ a)) ◇ ((z ◇ (a ◇ a)) ◇ t) = t := by
  have fix : a ◇ ((z ◇ (a ◇ a)) ◇ (z ◇ (a ◇ a))) = z ◇ (a ◇ a) := (h (z ◇ (a ◇ a)) a z).symm
  have e := h t (z ◇ (a ◇ a)) a
  rw [fix] at e
  exact e.symm

/-- Left translation by `z ◇ (a ◇ a)` is left translation by `a`, whatever `z` is. -/
theorem left_eq (a z v : G) : (z ◇ (a ◇ a)) ◇ v = a ◇ v := by
  have e := h ((z ◇ (a ◇ a)) ◇ v) a z
  rw [left_invol_aux h a z v] at e
  exact e

/-- Every left translation is an involution. -/
theorem left_invol (x y : G) : x ◇ (x ◇ y) = y := by
  have e := h y x x
  rw [left_eq h x x y] at e
  exact e.symm

/-- Squaring is injective. No finiteness used. -/
theorem sq_inj (a b : G) (e : a ◇ a = b ◇ b) : a = b := by
  have l : a ◇ b = b ◇ b := by
    rw [← left_eq h a a b, e, left_eq h b a b]
  calc a = a ◇ (a ◇ a) := (left_invol h a a).symm
    _ = a ◇ (b ◇ b) := by rw [e]
    _ = a ◇ (a ◇ b) := by rw [l]
    _ = b := left_invol h a b

/-- If squaring is surjective, 1763 follows. This is the only place finiteness would enter. -/
theorem law1763_of_sq_surj (sq : ∀ z : G, ∃ c : G, c ◇ c = z) (x y z : G) :
    x = (y ◇ z) ◇ ((x ◇ z) ◇ x) := by
  have ⟨c, hc⟩ := sq z
  subst hc
  rw [left_eq h c y, left_eq h c x, left_invol h c x]

end Law1167

#print axioms Law1167.left_invol
#print axioms Law1167.sq_inj
#print axioms Law1167.law1763_of_sq_surj

/-! ## The pigeonhole step, by hand -/

namespace Pigeon

theorem surj_of_inj : ∀ (n : Nat) (g : Nat → Nat),
    (∀ i, i < n → g i < n) → (∀ i j, i < n → j < n → g i = g j → i = j) →
    ∀ y, y < n → ∃ x, x < n ∧ g x = y := by
  intro n
  induction n with
  | zero =>
    intro _ _ _ y hy
    exact absurd hy (Nat.not_lt_zero y)
  | succ n ih =>
    intro g hb hi y hy
    have top : ∀ i, i < n → g n ≠ g i := fun i hl e =>
      Nat.lt_irrefl n (Nat.lt_of_le_of_lt
        (Nat.le_of_eq (hi n i (Nat.lt_succ_self n) (Nat.lt_succ_of_lt hl) e)) hl)
    have below : ∀ a, a < n + 1 → a ≠ n → a < n := fun a ha ne =>
      Nat.lt_of_le_of_ne (Nat.le_of_lt_succ ha) ne
    let g' : Nat → Nat := fun i => if g i = n then g n else g i
    have hb' : ∀ i, i < n → g' i < n := by
      intro i hl
      by_cases h : g i = n
      · have e : g' i = g n := if_pos h
        rw [e]
        exact below _ (hb n (Nat.lt_succ_self n)) (fun k => top i hl (k.trans h.symm))
      · have e : g' i = g i := if_neg h
        rw [e]
        exact below _ (hb i (Nat.lt_succ_of_lt hl)) h
    have hi' : ∀ i j, i < n → j < n → g' i = g' j → i = j := by
      intro i j hl hm e
      by_cases h1 : g i = n
      · by_cases h2 : g j = n
        · exact hi i j (Nat.lt_succ_of_lt hl) (Nat.lt_succ_of_lt hm) (h1.trans h2.symm)
        · have e1 : g' i = g n := if_pos h1
          have e2 : g' j = g j := if_neg h2
          rw [e1, e2] at e
          exact absurd e (top j hm)
      · by_cases h2 : g j = n
        · have e1 : g' i = g i := if_neg h1
          have e2 : g' j = g n := if_pos h2
          rw [e1, e2] at e
          exact absurd e.symm (top i hl)
        · have e1 : g' i = g i := if_neg h1
          have e2 : g' j = g j := if_neg h2
          rw [e1, e2] at e
          exact hi i j (Nat.lt_succ_of_lt hl) (Nat.lt_succ_of_lt hm) e
    by_cases hk : y = g n
    · exact ⟨n, Nat.lt_succ_self n, hk.symm⟩
    · by_cases hn : y = n
      · have hkn : g n ≠ n := fun k => hk (hn.trans k.symm)
        have ⟨i, hl, e⟩ := ih g' hb' hi' (g n) (below _ (hb n (Nat.lt_succ_self n)) hkn)
        by_cases h : g i = n
        · exact ⟨i, Nat.lt_succ_of_lt hl, h.trans hn.symm⟩
        · have e1 : g' i = g i := if_neg h
          rw [e1] at e
          exact absurd e.symm (top i hl)
      · have ⟨i, hl, e⟩ := ih g' hb' hi' y (below y hy hn)
        by_cases h : g i = n
        · have e1 : g' i = g n := if_pos h
          rw [e1] at e
          exact absurd e.symm hk
        · have e1 : g' i = g i := if_neg h
          rw [e1] at e
          exact ⟨i, Nat.lt_succ_of_lt hl, e⟩

theorem fin_surj_of_inj {n : Nat} (s : Fin n → Fin n) (hs : ∀ a b, s a = s b → a = b) (y : Fin n) :
    ∃ x, s x = y := by
  let g : Nat → Nat := fun i => if h : i < n then (s ⟨i, h⟩).val else 0
  have gv : ∀ i (h : i < n), g i = (s ⟨i, h⟩).val := fun i h => dif_pos h
  have ⟨x, hx, e⟩ := surj_of_inj n g
    (fun i h => by rw [gv i h]; exact (s ⟨i, h⟩).isLt)
    (fun i j hi hj e => by
      rw [gv i hi, gv j hj] at e
      exact congrArg Fin.val (hs ⟨i, hi⟩ ⟨j, hj⟩ (Fin.eq_of_val_eq e)))
    y.val y.isLt
  rw [gv x hx] at e
  exact ⟨⟨x, hx⟩, Fin.eq_of_val_eq e⟩

end Pigeon

/-- No finite countermodel, on any carrier size: every magma on `Fin n` satisfying 1167 satisfies 1763. -/
theorem no_finite_countermodel (n : Nat) [Magma (Fin n)]
    (h : ∀ x y z : Fin n, x = y ◇ ((z ◇ (y ◇ y)) ◇ x)) (x y z : Fin n) :
    x = (y ◇ z) ◇ ((x ◇ z) ◇ x) :=
  Law1167.law1763_of_sq_surj h
    (fun z => Pigeon.fin_surj_of_inj (fun a => a ◇ a) (Law1167.sq_inj h) z) x y z

#print axioms Pigeon.fin_surj_of_inj
#print axioms no_finite_countermodel
