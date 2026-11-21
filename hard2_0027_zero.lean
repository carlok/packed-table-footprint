import JudgeProblem

namespace submission
/-! Remainder from the fuel definitions of `Nat.mod` and `Nat.modCore`, because core's own `%` lemmas close over `propext`. -/

theorem add_sub_cancel' (a : Nat) : ∀ y : Nat, a + y - y = a
  | 0 => rfl
  | y + 1 => by
    show (a + y).succ - y.succ = a
    rw [Nat.succ_sub_succ]
    exact add_sub_cancel' a y

theorem modCore_eq_go (x y : Nat) (hy : 0 < y) :
    Nat.modCore x y = Nat.modCore.go y hy (x + 1) x (Nat.lt_succ_self x) := by
  unfold Nat.modCore
  exact dif_pos hy

theorem mod_succ_of_le (n y : Nat) (h : y ≤ n + 1) : (n + 1) % y = Nat.modCore (n + 1) y := by
  show Nat.mod (n + 1) y = _
  exact if_pos h

theorem mod_succ_of_not_le (n y : Nat) (h : ¬ y ≤ n + 1) : (n + 1) % y = n + 1 := by
  show Nat.mod (n + 1) y = _
  exact if_neg h

theorem step {y q r x f : Nat} (hy : 0 < y) (h : x < f + 1) (e : x = (q + 1) * y + r) :
    y ≤ x ∧ x - y = q * y + r ∧ q * y + r < f := by
  have ex : x = (q * y + r) + y := by
    rw [e, Nat.succ_mul, Nat.add_assoc, Nat.add_comm y r, ← Nat.add_assoc]
  have h2 : (q * y + r) + y < f + 1 := by
    rw [← ex]
    exact h
  refine ⟨?_, ?_, ?_⟩
  · rw [ex]
    exact Nat.le_add_left y _
  · rw [ex]
    exact add_sub_cancel' _ _
  · exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hy) (Nat.le_of_lt_succ h2)

theorem mod_go_spec {y r : Nat} (hy : 0 < y) (hr : r < y) (q : Nat) :
    ∀ (fuel x : Nat) (h : x < fuel), x = q * y + r → Nat.modCore.go y hy fuel x h = r := by
  induction q with
  | zero =>
    intro fuel x h e
    cases fuel with
    | zero => exact absurd h (Nat.not_lt_zero _)
    | succ f =>
      have hn : ¬ y ≤ x := by
        rw [e, Nat.zero_mul, Nat.zero_add]
        exact Nat.not_le_of_gt hr
      have : Nat.modCore.go y hy (f + 1) x h = x := by
        rw [Nat.modCore.go]
        exact dif_neg hn
      rw [this, e, Nat.zero_mul, Nat.zero_add]
  | succ q ih =>
    intro fuel x h e
    cases fuel with
    | zero => exact absurd h (Nat.not_lt_zero _)
    | succ f =>
      have ⟨hle, hsub, hlt⟩ := step hy h e
      have hs : x - y < f := by
        rw [hsub]
        exact hlt
      have : Nat.modCore.go y hy (f + 1) x h = Nat.modCore.go y hy f (x - y) hs := by
        rw [Nat.modCore.go]
        exact dif_pos hle
      rw [this, ih f (x - y) hs hsub]

theorem mod_spec {y r : Nat} (q : Nat) (hr : r < y) : (q * y + r) % y = r := by
  have hy : 0 < y := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  generalize hx : q * y + r = x
  cases x with
  | zero =>
    have h0 : r ≤ 0 := by
      rw [← hx]
      exact Nat.le_add_left r _
    rw [Nat.zero_mod]
    exact (Nat.le_antisymm h0 (Nat.zero_le r)).symm
  | succ n =>
    cases Nat.lt_or_ge (n + 1) y with
    | inl hlt =>
      rw [mod_succ_of_not_le n y (Nat.not_le_of_gt hlt)]
      cases q with
      | zero =>
        rw [Nat.zero_mul, Nat.zero_add] at hx
        exact hx.symm
      | succ q =>
        exfalso
        have : y ≤ n + 1 := by
          rw [← hx, Nat.succ_mul, Nat.add_assoc, Nat.add_comm y r, ← Nat.add_assoc]
          exact Nat.le_add_left y _
        exact Nat.not_le_of_gt hlt this
    | inr hge =>
      rw [mod_succ_of_le n y hge, modCore_eq_go _ y hy]
      exact mod_go_spec hy hr q _ _ _ hx.symm

/-! Parity, in place of the eight `omega` lemmas. -/

theorem even_or_odd : ∀ n : Nat, (∃ q, n = q * 2) ∨ (∃ q, n = q * 2 + 1)
  | 0 => Or.inl ⟨0, rfl⟩
  | n + 1 =>
    match even_or_odd n with
    | Or.inl ⟨q, e⟩ => Or.inr ⟨q, by rw [e]⟩
    | Or.inr ⟨q, e⟩ => Or.inl ⟨q + 1, by rw [e, Nat.succ_mul]⟩

theorem flip (n : Nat) : (n % 2 = 0 ∧ (n + 1) % 2 = 1) ∨ (n % 2 = 1 ∧ (n + 1) % 2 = 0) :=
  match even_or_odd n with
  | Or.inl ⟨q, e⟩ =>
    Or.inl ⟨by rw [e]; exact mod_spec (y := 2) (r := 0) q (by decide),
            by rw [e]; exact mod_spec (y := 2) (r := 1) q (by decide)⟩
  | Or.inr ⟨q, e⟩ =>
    Or.inr ⟨by rw [e]; exact mod_spec (y := 2) (r := 1) q (by decide),
            by rw [e]; show (q * 2 + 2) % 2 = 0; rw [← Nat.succ_mul]; exact mod_spec (y := 2) (r := 0) (q + 1) (by decide)⟩

theorem mod_two_add_two (n : Nat) : (n + 2) % 2 = n % 2 :=
  match flip n, flip (n + 1) with
  | Or.inl ⟨a, _⟩, Or.inr ⟨_, c⟩ => c.trans a.symm
  | Or.inr ⟨a, _⟩, Or.inl ⟨_, c⟩ => c.trans a.symm
  | Or.inl ⟨_, b⟩, Or.inl ⟨d, _⟩ => absurd (b.symm.trans d) (by decide)
  | Or.inr ⟨_, b⟩, Or.inr ⟨d, _⟩ => absurd (b.symm.trans d) (by decide)

theorem mod_two_ne_down_to (n m : Nat) : (n + 1) % 2 = m % 2 → ¬ n % 2 = m % 2 := fun h k =>
  match flip n with
  | Or.inl ⟨a, b⟩ => absurd (a.symm.trans (k.trans (h.symm.trans b))) (by decide)
  | Or.inr ⟨a, b⟩ => absurd (a.symm.trans (k.trans (h.symm.trans b))) (by decide)

theorem mod_two_eq_down_to (n m : Nat) : (n + 1) % 2 ≠ m % 2 → n % 2 = m % 2 := fun h =>
  match flip n, flip m with
  | Or.inl ⟨a, _⟩, Or.inl ⟨c, _⟩ => a.trans c.symm
  | Or.inr ⟨a, _⟩, Or.inr ⟨c, _⟩ => a.trans c.symm
  | Or.inl ⟨_, b⟩, Or.inr ⟨c, _⟩ => absurd (b.trans c.symm) h
  | Or.inr ⟨_, b⟩, Or.inl ⟨c, _⟩ => absurd (b.trans c.symm) h

def f (x : Nat) (y : Nat) : Nat :=
  match x with
  | 0 =>
    if y % 2 = 0
    then 1 else 0
  | n + 1 =>
    if x % 2 = y % 2
    then n + 2 else n

/-! `f x y` applies one of two involutions to `x`, chosen by the parity of `y`. -/

theorem f_mod_congr (x : Nat) {a b : Nat} (h : a % 2 = b % 2) : f x a = f x b := by
  cases x with
  | zero =>
    show (if a % 2 = 0 then 1 else 0) = (if b % 2 = 0 then 1 else 0)
    rw [h]
  | succ n =>
    show (if (n + 1) % 2 = a % 2 then n + 2 else n) = (if (n + 1) % 2 = b % 2 then n + 2 else n)
    rw [h]

theorem f_self : ∀ y : Nat, f y y = y + 1
  | 0 => rfl
  | _ + 1 => if_pos rfl

theorem f_succ_mod (y z : Nat) : f (y + 1) z % 2 = y % 2 := by
  by_cases h : (y + 1) % 2 = z % 2
  · have e : f (y + 1) z = y + 2 := if_pos h
    rw [e]
    exact mod_two_add_two y
  · have e : f (y + 1) z = y := if_neg h
    rw [e]

theorem f_invol (x y : Nat) : f (f x y) y = x := by
  cases x with
  | zero =>
    by_cases h : y % 2 = 0
    · have e : f 0 y = 1 := if_pos h
      rw [e]
      show (if (0 + 1) % 2 = y % 2 then 0 + 2 else 0) = 0
      exact if_neg (fun k => absurd (k.trans h) (by decide))
    · have e : f 0 y = 0 := if_neg h
      rw [e, e]
  | succ n =>
    by_cases h : (n + 1) % 2 = y % 2
    · have e : f (n + 1) y = n + 2 := if_pos h
      rw [e]
      show (if (n + 2) % 2 = y % 2 then n + 3 else n + 1) = n + 1
      exact if_neg (fun k => mod_two_ne_down_to (n + 1) y k h)
    · have e : f (n + 1) y = n := if_neg h
      rw [e]
      cases n with
      | zero =>
        have k : y % 2 = 0 := (mod_two_eq_down_to 0 y h).symm
        exact if_pos k
      | succ m =>
        exact if_pos (mod_two_eq_down_to (m + 1) y h)

theorem f_1659 :
  ∀ (x y z : Nat),
  x = f (f x y) (f (f y y) z ) := by
  intro x y z
  rw [f_self, f_mod_congr (f x y) (f_succ_mod y z), f_invol]

theorem impl (G : Type) [Magma G] (h : ∀ x y z : G, x = (x ◇ y) ◇ ((y ◇ y) ◇ z)) :
    ∀ x y z : G, x = (x ◇ ((y ◇ y) ◇ z)) ◇ y := by
  have e0 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := by
    exact (h X0 X1 X2).symm
  have e1 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := by
    exact (congrArg (fun q => ((X0 ◇ X1) ◇ q)) (e0 X1 X1 X0)).symm.trans
      (e0 X0 X1 ((X1 ◇ X1) ◇ X0))
  have e2 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := by
    exact (congrArg (fun q => (q ◇ ((X1 ◇ X1) ◇ X2))) (e1 X0 X1)).symm.trans
      (e0 (X0 ◇ X1) X1 X2)
  intro x y z
  exact (congrArg (fun q => q ◇ y) (e2 x y z)).trans (e1 x y) |>.symm

theorem f_2473 : ∀ x y z : Nat, x = f (f x (f (f y y) z)) y :=
  @impl Nat ⟨f⟩ f_1659

end submission

def submission : Goal := by
  refine ⟨Nat, ⟨fun x y => submission.f y x⟩, ?_, ?_⟩
  · intro x y z
    exact submission.f_2473 x y z
  · intro h
    exact absurd (h 0 1 0) (by decide)
