import JudgeProblem

namespace submission

/-- `(false, n)` is `n`, `(true, n)` is `-n-1`. -/
abbrev Z := Bool × Nat

def succ : Z → Z
  | (false, n) => (false, n + 1)
  | (true, 0) => (false, 0)
  | (true, n + 1) => (true, n)

def pred : Z → Z
  | (false, 0) => (true, 0)
  | (false, n + 1) => (false, n)
  | (true, n) => (true, n + 1)

theorem pred_succ : ∀ x, pred (succ x) = x
  | (false, _) => rfl
  | (true, 0) => rfl
  | (true, _ + 1) => rfl

theorem succ_pred : ∀ x, succ (pred x) = x
  | (false, 0) => rfl
  | (false, _ + 1) => rfl
  | (true, _) => rfl

def addN (x : Z) : Nat → Z
  | 0 => x
  | n + 1 => succ (addN x n)

def subN (x : Z) : Nat → Z
  | 0 => x
  | n + 1 => pred (subN x n)

def add (x : Z) : Z → Z
  | (false, n) => addN x n
  | (true, n) => pred (subN x n)

def neg : Z → Z
  | (false, 0) => (false, 0)
  | (false, n + 1) => (true, n)
  | (true, n) => (false, n + 1)

def sub (a b : Z) : Z := add a (neg b)

theorem zind {P : Z → Prop} (h0 : P (false, 0)) (hs : ∀ y, P y → P (succ y)) (hp : ∀ y, P y → P (pred y)) :
    ∀ y, P y
  | (false, n) => by
    induction n with
    | zero => exact h0
    | succ n ih => exact hs _ ih
  | (true, n) => by
    induction n with
    | zero => exact hp _ h0
    | succ n ih => exact hp _ ih

theorem add_succ (x : Z) : ∀ y, add x (succ y) = succ (add x y)
  | (false, _) => rfl
  | (true, 0) => (succ_pred x).symm
  | (true, _ + 1) => (succ_pred _).symm

theorem add_pred (x : Z) : ∀ y, add x (pred y) = pred (add x y)
  | (false, 0) => rfl
  | (false, _ + 1) => (pred_succ _).symm
  | (true, _) => rfl

theorem succ_add (a : Z) : ∀ b, add (succ a) b = succ (add a b) :=
  zind rfl
    (fun y ih => by rw [add_succ, add_succ, ih])
    (fun y ih => by rw [add_pred, add_pred, ih, pred_succ, succ_pred])

theorem pred_add (a : Z) : ∀ b, add (pred a) b = pred (add a b) :=
  zind rfl
    (fun y ih => by rw [add_succ, add_succ, ih, pred_succ, succ_pred])
    (fun y ih => by rw [add_pred, add_pred, ih])

theorem zero_add : ∀ b : Z, add (false, 0) b = b :=
  zind rfl
    (fun y ih => by rw [add_succ, ih])
    (fun y ih => by rw [add_pred, ih])

theorem assoc (a b : Z) : ∀ c, add (add a b) c = add a (add b c) :=
  zind rfl
    (fun y ih => by rw [add_succ, add_succ, add_succ, ih])
    (fun y ih => by rw [add_pred, add_pred, add_pred, ih])

theorem comm (a : Z) : ∀ b, add a b = add b a :=
  zind (zero_add a).symm
    (fun y ih => by rw [add_succ, succ_add, ih])
    (fun y ih => by rw [add_pred, pred_add, ih])

theorem neg_succ : ∀ a, neg (succ a) = pred (neg a)
  | (false, 0) => rfl
  | (false, _ + 1) => rfl
  | (true, 0) => rfl
  | (true, _ + 1) => rfl

theorem neg_pred : ∀ a, neg (pred a) = succ (neg a)
  | (false, 0) => rfl
  | (false, 0 + 1) => rfl
  | (false, _ + 1 + 1) => rfl
  | (true, _) => rfl

theorem add_neg : ∀ a : Z, add a (neg a) = (false, 0) :=
  zind rfl
    (fun y ih => by rw [neg_succ, add_pred, succ_add, pred_succ, ih])
    (fun y ih => by rw [neg_pred, add_succ, pred_add, succ_pred, ih])

theorem neg_add (b : Z) : ∀ e, neg (add b e) = add (neg b) (neg e) :=
  zind (by show neg b = neg b; rfl)
    (fun y ih => by rw [add_succ, neg_succ, neg_succ, add_pred, ih])
    (fun y ih => by rw [add_pred, neg_pred, neg_pred, add_succ, ih])

theorem neg_neg : ∀ a : Z, neg (neg a) = a
  | (false, 0) => rfl
  | (false, _ + 1) => rfl
  | (true, _) => rfl

theorem sub_rev (a b : Z) : sub a b = neg (sub b a) := by
  unfold sub
  rw [neg_add, neg_neg, comm]

theorem sub_self (a : Z) : sub a a = (false, 0) := add_neg a

theorem sub_add (a b c e : Z) : sub (add b e) (add a c) = add (sub b a) (sub e c) := by
  unfold sub
  rw [neg_add, assoc, assoc, ← assoc e (neg a), comm e (neg a), assoc (neg a) e (neg c)]


def H : Z → Bool × Z
  | (false, 0) => (false, (true, 1))
  | (false, 1) => (false, (true, 0))
  | (false, 2) => (false, (false, 0))
  | (false, _ + 3) => (true, (true, 1))
  | (true, 0) => (false, (true, 2))
  | (true, 1) => (false, (false, 2))
  | (true, _ + 2) => (true, (false, 1))

/-- `x + c` or `y + e`, as `H (y - x)` says. -/
def f (a b : Z) : Z :=
  match H (sub b a) with
  | (false, c) => add a c
  | (true, e) => add b e

theorem a0 (a b c e c' : Z) {D c2 : Z} (hD : sub b a = D) (h : H (add D (sub e c)) = (false, c2))
    (hc : add c c2 = c') : f (add a c) (add b e) = add a c' := by
  unfold f; rw [sub_add, hD, h]; show add (add a c) c2 = _; rw [assoc, hc]

theorem a1 (a b c e e' : Z) {D e2 : Z} (hD : sub b a = D) (h : H (add D (sub e c)) = (true, e2))
    (hc : add e e2 = e') : f (add a c) (add b e) = add b e' := by
  unfold f; rw [sub_add, hD, h]; show add (add b e) e2 = _; rw [assoc, hc]

theorem add_sub' (b a : Z) : add a (sub b a) = b := by
  unfold sub
  rw [comm b, ← assoc, add_neg, zero_add]

theorem cross (x y c1 c2 : Z) {D : Z} (h : sub x y = D) (hc : add D c1 = c2) : add x c1 = add y c2 := by
  rw [← hc, ← h, ← assoc, add_sub']

theorem law (x y : Z) : x = (f y (f x (f y x))) := by
  generalize h : sub x y = d
  cases d with
  | mk s n =>
  cases s with
  | false => (cases n with | zero => (exact (rfl : x = add x (false, 0)).trans ((cross x y (false, 0) (false, 0) h rfl).trans ((congr (congrArg f (rfl : y = add y (false, 0))) ((congr (congrArg f (rfl : x = add x (false, 0))) ((congr (congrArg f (rfl : y = add y (false, 0))) (rfl : x = add x (false, 0))).trans (a0 y x (false, 0) (false, 0) (true, 1) h rfl rfl))).trans (a0 x y (false, 0) (true, 1) (false, 2) ((sub_rev y x).trans (congrArg neg h)) rfl rfl))).trans (a0 y x (false, 0) (false, 2) (false, 0) h rfl rfl)).symm)) | succ n => (cases n with | zero => (exact (rfl : x = add x (false, 0)).trans ((congr (congrArg f (rfl : y = add y (false, 0))) ((congr (congrArg f (rfl : x = add x (false, 0))) ((congr (congrArg f (rfl : y = add y (false, 0))) (rfl : x = add x (false, 0))).trans (a0 y x (false, 0) (false, 0) (true, 0) h rfl rfl))).trans (a0 x y (false, 0) (true, 0) (false, 2) ((sub_rev y x).trans (congrArg neg h)) rfl rfl))).trans (a1 y x (false, 0) (false, 2) (false, 0) h rfl rfl)).symm) | succ n => (cases n with | zero => (exact (rfl : x = add x (false, 0)).trans ((congr (congrArg f (rfl : y = add y (false, 0))) ((congr (congrArg f (rfl : x = add x (false, 0))) ((congr (congrArg f (rfl : y = add y (false, 0))) (rfl : x = add x (false, 0))).trans (a0 y x (false, 0) (false, 0) (false, 0) h rfl rfl))).trans (a0 x y (false, 0) (false, 0) (false, 2) ((sub_rev y x).trans (congrArg neg h)) rfl rfl))).trans (a1 y x (false, 0) (false, 2) (false, 0) h rfl rfl)).symm) | succ n => (exact (rfl : x = add x (false, 0)).trans ((congr (congrArg f (rfl : y = add y (false, 0))) ((congr (congrArg f (rfl : x = add x (false, 0))) ((congr (congrArg f (rfl : y = add y (false, 0))) (rfl : x = add x (false, 0))).trans (a1 y x (false, 0) (false, 0) (true, 1) h rfl rfl))).trans (a0 x x (false, 0) (true, 1) (false, 2) (sub_self x) rfl rfl))).trans (a1 y x (false, 0) (false, 2) (false, 0) h rfl rfl)).symm))))
  | true => (cases n with | zero => (exact (rfl : x = add x (false, 0)).trans ((cross x y (false, 0) (true, 0) h rfl).trans ((congr (congrArg f (rfl : y = add y (false, 0))) ((congr (congrArg f (rfl : x = add x (false, 0))) ((congr (congrArg f (rfl : y = add y (false, 0))) (rfl : x = add x (false, 0))).trans (a0 y x (false, 0) (false, 0) (true, 2) h rfl rfl))).trans (a0 x y (false, 0) (true, 2) (false, 2) ((sub_rev y x).trans (congrArg neg h)) rfl rfl))).trans (a0 y x (false, 0) (false, 2) (true, 0) h rfl rfl)).symm)) | succ n => (cases n with | zero => (exact (rfl : x = add x (false, 0)).trans ((cross x y (false, 0) (true, 1) h rfl).trans ((congr (congrArg f (rfl : y = add y (false, 0))) ((congr (congrArg f (rfl : x = add x (false, 0))) ((congr (congrArg f (rfl : y = add y (false, 0))) (rfl : x = add x (false, 0))).trans (a0 y x (false, 0) (false, 0) (false, 2) h rfl rfl))).trans (a1 x y (false, 0) (false, 2) (false, 0) ((sub_rev y x).trans (congrArg neg h)) rfl rfl))).trans (a0 y y (false, 0) (false, 0) (true, 1) (sub_self y) rfl rfl)).symm)) | succ n => (exact (rfl : x = add x (false, 0)).trans ((congr (congrArg f (rfl : y = add y (false, 0))) ((congr (congrArg f (rfl : x = add x (false, 0))) ((congr (congrArg f (rfl : y = add y (false, 0))) (rfl : x = add x (false, 0))).trans (a1 y x (false, 0) (false, 0) (false, 1) h rfl rfl))).trans (a0 x x (false, 0) (false, 1) (true, 0) (sub_self x) rfl rfl))).trans (a1 y x (false, 0) (true, 0) (false, 0) h rfl rfl)).symm)))

instance mag : Magma Z := ⟨f⟩

theorem lhs : EquationLHS Z := fun x y => law x y

theorem rhs : ¬ EquationRHS Z :=
  fun h => absurd (h (false, 0) (false, 1)) (by decide)

end submission

def submission : Goal := ⟨submission.Z, submission.mag, submission.lhs, submission.rhs⟩
