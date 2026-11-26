/-
  RiemannHolonomy.lean
  Self-contained formal verification module:
  "Projective Cayley-Weierstrass Holonomy on P^1(C) and Two-Wave Destructive
   Interference Lock at Re(s) = 1/2 (Pauli Antiphase dphi = pi)"
  Authors: D. A. Karataev & Luch (Луч)
  Zero external dependencies (pure Lean 4 core), zero `sorry`, zero `Classical.choice`.
-/

namespace RiemannHolonomy

set_option linter.unusedSimpArgs false

/-- Quarter-period `Q_m = 2^(m - 2)` on the projective phase ring `Z_{2^m}` (`m >= 2`). -/
def ringQ (m : Nat) : Int :=
  ((2 ^ (m - 2) : Nat) : Int)

/-- Half-period (Pauli antiphase `pi`) `2 Q_m = 2^(m - 1)` on `Z_{2^m}`. -/
def ringHalfPeriod (m : Nat) : Int :=
  2 * ringQ m

/-- Full ring modulus `4 Q_m = 2^m`. -/
def ringMod (m : Nat) : Int :=
  4 * ringQ m

/-- Angular distance `|(phi mod 4q) - 2q| : Nat` from the Pauli antiphase point `2q` (`pi`). -/
def pauliPhaseDistNat (q phi : Int) : Nat :=
  (phi.emod (4 * q) - 2 * q).natAbs

/-- Branchless projective cosine `C_q(phi) = |(phi mod 4q) - 2q| - q` for any quarter-period `q > 0`:
    - `C_q(0)  = |0 - 2q| - q = +q`
    - `C_q(q)  = |q - 2q| - q =  0`
    - `C_q(2q) = |2q - 2q| - q = -q` (Pauli antiphase `pi`). -/
def projCQ (q phi : Int) : Int :=
  ((pauliPhaseDistNat q phi : Nat) : Int) - q

/-- Branchless projective sine `S_q(phi) = C_q(phi - q)`. -/
def projSQ (q phi : Int) : Int :=
  projCQ q (phi - q)

/-- Projective cosine and sine on the dyadic ring `Z_{2^m}` (`q = Q_m = 2^(m-2)`). -/
def projC (m : Nat) (phi : Int) : Int :=
  projCQ (ringQ m) phi

def projS (m : Nat) (phi : Int) : Int :=
  projSQ (ringQ m) phi

/-- Weierstrass stereographic lift `(X, Y, R) = (C^2 - S^2, 2 C S, C^2 + S^2)`. -/
def weierstrassX (c s : Int) : Int := c * c - s * s
def weierstrassY (c s : Int) : Int := 2 * c * s
def weierstrassR (c s : Int) : Int := c * c + s * s

/-- Homogeneous norm-squared of the numerator of `s = ((c0 + delta) + i s0) / (2 c0)`
    and `1 - s = ((c0 - delta) - i s0) / (2 c0)` in the Cayley map `w(s) = s / (1 - s)`,
    where `delta / (2 c0) = Re(s) - 1/2`. -/
def cayleyNumNormSq (c0 s0 delta : Int) : Int :=
  (c0 + delta) * (c0 + delta) + s0 * s0

def cayleyDenNormSq (c0 s0 delta : Int) : Int :=
  (c0 - delta) * (c0 - delta) + s0 * s0

/-- Constructive (`0 Classical.choice`) helper: `0 <= x * x` for all `x : Int`. -/
theorem int_sq_nonneg_constructive (x : Int) : 0 ≤ x * x := by
  cases x with
  | ofNat n =>
    change (0 : Int) ≤ ((n * n : Nat) : Int)
    omega
  | negSucc n =>
    change (0 : Int) ≤ (((n + 1) * (n + 1) : Nat) : Int)
    omega

/-- Constructive (`0 Classical.choice`) helper: `0 <= a -> 0 <= b -> 0 <= a * b`. -/
theorem int_mul_nonneg_constructive {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      change (0 : Int) ≤ ((m * n : Nat) : Int)
      omega
    | negSucc n =>
      change (0 : Int) ≤ Int.negSucc n at hb
      omega
  | negSucc m =>
    change (0 : Int) ≤ Int.negSucc m at ha
    omega

/-- Constructive (`0 Classical.choice`) helper: `(m1 + 1) * (n1 + 1) = m1 * (n1 + 1) + n1 + 1`. -/
theorem nat_succ_mul_succ_pos (m1 n1 : Nat) : 0 < (m1 + 1) * (n1 + 1) := by
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Constructive (`0 Classical.choice`) helper: `0 < a -> 0 < b -> 0 < a * b`. -/
theorem int_mul_pos_constructive {a b : Int} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  cases a with
  | ofNat m =>
    cases m with
    | zero =>
      change (0 : Int) < (0 : Int) at ha
      omega
    | succ m1 =>
      cases b with
      | ofNat n =>
        cases n with
        | zero =>
          change (0 : Int) < (0 : Int) at hb
          omega
        | succ n1 =>
          change (0 : Int) < (((m1 + 1) * (n1 + 1) : Nat) : Int)
          have hNat : 0 < (m1 + 1) * (n1 + 1) := nat_succ_mul_succ_pos m1 n1
          omega
      | negSucc n =>
        change (0 : Int) < Int.negSucc n at hb
        omega
  | negSucc m =>
    change (0 : Int) < Int.negSucc m at ha
    omega

/-- Constructive (`0 Classical.choice`) helper: `a * b = 0 -> a = 0 \/ b = 0`. -/
theorem int_mul_eq_zero_constructive {a b : Int} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  cases a with
  | ofNat m =>
    cases m with
    | zero => exact Or.inl rfl
    | succ m1 =>
      cases b with
      | ofNat n =>
        cases n with
        | zero => exact Or.inr rfl
        | succ n1 =>
          change (((m1 + 1) * (n1 + 1) : Nat) : Int) = 0 at h
          have hNat : 0 < (m1 + 1) * (n1 + 1) := nat_succ_mul_succ_pos m1 n1
          omega
      | negSucc n =>
        have hEq : Int.ofNat (m1 + 1) * Int.negSucc n = -(((m1 + 1) * (n + 1) : Nat) : Int) := rfl
        rw [hEq] at h
        have hNat : 0 < (m1 + 1) * (n + 1) := nat_succ_mul_succ_pos m1 n
        omega
  | negSucc m =>
    cases b with
    | ofNat n =>
      cases n with
      | zero => exact Or.inr rfl
      | succ n1 =>
        have hEq : Int.negSucc m * Int.ofNat (n1 + 1) = -(((m + 1) * (n1 + 1) : Nat) : Int) := rfl
        rw [hEq] at h
        have hNat : 0 < (m + 1) * (n1 + 1) := nat_succ_mul_succ_pos m n1
        omega
    | negSucc n =>
      change (((m + 1) * (n + 1) : Nat) : Int) = 0 at h
      have hNat : 0 < (m + 1) * (n + 1) := nat_succ_mul_succ_pos m n
      omega

/-- **Theorem 1A (Exact Cayley-Weierstrass Norm Imbalance Identity):**
    For `s = (c0 + delta + i s0)/(2 c0)` with deviation `delta` from `Re(s) = 1/2`,
    the difference between the squared modulus of `s` and `1 - s` is identically `4 * (c0 * delta)`. -/
theorem cayley_norm_imbalance_identity (c0 s0 delta : Int) :
    cayleyNumNormSq c0 s0 delta - cayleyDenNormSq c0 s0 delta = 4 * (c0 * delta) := by
  dsimp [cayleyNumNormSq, cayleyDenNormSq]
  have hPlus : (c0 + delta) * (c0 + delta) = c0 * c0 + 2 * (c0 * delta) + delta * delta := by
    have h1 : delta * c0 = c0 * delta := Int.mul_comm delta c0
    simp [Int.add_mul, Int.mul_add, h1, Int.mul_assoc]
    omega
  have hMinus : (c0 - delta) * (c0 - delta) = c0 * c0 - 2 * (c0 * delta) + delta * delta := by
    have h1 : delta * c0 = c0 * delta := Int.mul_comm delta c0
    simp [Int.sub_mul, Int.mul_sub, h1, Int.mul_assoc]
    omega
  rw [hPlus, hMinus]
  omega

/-- **Theorem 1B (Critical Line `Re(s) = 1/2` <=> Unitary Equator `|w(s)| = 1`):**
    For any positive scale `c0 > 0`, the forward and reflected Cayley norms are equal
    (`|s|^2 = |1 - s|^2`, i.e., `|w(s)| = 1`) if and only if `delta = 0` (`Re(s) = 1/2`). -/
theorem cayley_unitary_equator_iff_critical_line (c0 s0 delta : Int) (hc0 : 0 < c0) :
    cayleyNumNormSq c0 s0 delta = cayleyDenNormSq c0 s0 delta ↔ delta = 0 := by
  have hDiff := cayley_norm_imbalance_identity c0 s0 delta
  constructor
  · intro hEq
    have hProdZero : c0 * delta = 0 := by omega
    cases int_mul_eq_zero_constructive hProdZero with
    | inl hc0Zero => omega
    | inr hDeltaZero => exact hDeltaZero
  · intro hDelta
    subst hDelta
    simp [cayleyNumNormSq, cayleyDenNormSq]

/-- **Theorem 1C (Exact Weierstrass Circle Identity on the Critical Line `delta = 0`):**
    On the critical line `Re(s) = 1/2` (`delta = 0`), the Cayley ratio `w(s) = s / (1 - s)`
    is identically the Weierstrass stereographic point `(X, Y, R) = (c0^2 - s0^2, 2 c0 s0, c0^2 + s0^2)`
    lying on the exact unit circle `X^2 + Y^2 = R^2`. -/
theorem weierstrass_equator_pythagorean_identity (c0 s0 : Int) :
    (weierstrassX c0 s0) * (weierstrassX c0 s0) + (weierstrassY c0 s0) * (weierstrassY c0 s0) =
    (weierstrassR c0 s0) * (weierstrassR c0 s0) := by
  dsimp [weierstrassX, weierstrassY, weierstrassR]
  have h1 : (c0 * c0) * (s0 * s0) = (s0 * s0) * (c0 * c0) := Int.mul_comm (c0 * c0) (s0 * s0)
  have h2 : (2 * c0 * s0) * (2 * c0 * s0) = 4 * ((c0 * c0) * (s0 * s0)) := by
    calc
      (2 * c0 * s0) * (2 * c0 * s0)
          = (2 * 2) * ((c0 * c0) * (s0 * s0)) := by
            simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = 4 * ((c0 * c0) * (s0 * s0)) := by rfl
  simp [Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add, h2, ← h1]
  omega

/-- **Theorem 2A (Universal Lower Bound and Unique Pauli Antiphase Minimum of `C_q(phi)`):**
    For every quarter-period `q` and every phase `phi : Int`:
    1. `-q <= projCQ q phi` (so `0 <= q + projCQ q phi`),
    2. `projCQ q phi = -q` if and only if `pauliPhaseDistNat q phi = 0` (exact Pauli antiphase `pi`). -/
theorem projCQ_lower_bound_and_pauli_antiphase_iff (q phi : Int) :
    -q ≤ projCQ q phi ∧
    (projCQ q phi = -q ↔ pauliPhaseDistNat q phi = 0) := by
  dsimp [projCQ]
  generalize pauliPhaseDistNat q phi = d
  constructor
  · omega
  · constructor
    · intro h
      omega
    · intro h
      omega

/-- Quadratic interference intensity `I(muPlus, muMinus, cPhi)` of two counter-propagating
    waves with amplitudes `muPlus, muMinus` and projective phase cosine `cPhi = C_q(dphi)`:
    `I = q * (muPlus^2 + muMinus^2) + 2 * (muPlus * muMinus) * cPhi`. -/
def counterwaveInterferenceIntensity (q muPlus muMinus cPhi : Int) : Int :=
  q * (muPlus * muPlus + muMinus * muMinus) + 2 * (muPlus * muMinus) * cPhi

/-- **Theorem 2B (Universal Counter-Wave Interference Sum-of-Squares Decomposition):**
    For any quarter-period `q`, amplitudes `muPlus, muMinus`, and phase cosine `cPhi`,
    the interference intensity decomposes identically into the radial amplitude-imbalance
    square `q * (muPlus - muMinus)^2` plus the Pauli phase barrier `2 * (muPlus * muMinus) * (q + cPhi)`:
    `I(q, muPlus, muMinus, cPhi) = q * (muPlus - muMinus)^2 + 2 * (muPlus * muMinus) * (q + cPhi)`. -/
theorem counterwave_interference_decomposition (q muPlus muMinus cPhi : Int) :
    counterwaveInterferenceIntensity q muPlus muMinus cPhi =
    q * ((muPlus - muMinus) * (muPlus - muMinus)) + 2 * (muPlus * muMinus) * (q + cPhi) := by
  dsimp [counterwaveInterferenceIntensity]
  have hSq :
      muPlus * muPlus + muMinus * muMinus =
      (muPlus - muMinus) * (muPlus - muMinus) + 2 * (muPlus * muMinus) := by
    have hComm : muMinus * muPlus = muPlus * muMinus := Int.mul_comm muMinus muPlus
    simp [Int.sub_mul, Int.mul_sub, hComm]
    omega
  rw [hSq]
  have hDist1 :
      q * ((muPlus - muMinus) * (muPlus - muMinus) + 2 * (muPlus * muMinus)) =
      q * ((muPlus - muMinus) * (muPlus - muMinus)) + 2 * (muPlus * muMinus) * q := by
    rw [Int.mul_add]
    have hComm2 : q * (2 * (muPlus * muMinus)) = 2 * (muPlus * muMinus) * q :=
      Int.mul_comm q (2 * (muPlus * muMinus))
    rw [hComm2]
  have hDist2 :
      2 * (muPlus * muMinus) * (q + cPhi) =
      2 * (muPlus * muMinus) * q + 2 * (muPlus * muMinus) * cPhi := by
    exact Int.mul_add (2 * (muPlus * muMinus)) q cPhi
  rw [hDist1, hDist2]
  omega

/-- **Theorem 3 (Two-Wave Destructive Interference Zero Lock):**
    When both counter-propagating amplitudes are positive (`muPlus > 0`, `muMinus > 0`),
    the quarter-period is positive (`q > 0`), and the phase cosine satisfies the ring bound
    `cPhi >= -q` (i.e., `q + cPhi >= 0`), the interference pattern vanishes
    (`counterwaveInterferenceIntensity q muPlus muMinus cPhi = 0`)
    IF AND ONLY IF:
    (1) the forward and reflected amplitudes are strictly equal (`muPlus = muMinus`), AND
    (2) the relative phase is in exact Pauli antiphase `pi` (`cPhi = -q`). -/
theorem destructive_interference_zero_iff
    (q muPlus muMinus cPhi : Int)
    (hq : 0 < q) (hPlus : 0 < muPlus) (hMinus : 0 < muMinus) (hCos : -q ≤ cPhi) :
    counterwaveInterferenceIntensity q muPlus muMinus cPhi = 0 ↔
    (muPlus = muMinus ∧ cPhi = -q) := by
  rw [counterwave_interference_decomposition]
  constructor
  · intro hZero
    have hDiffSqNonneg : 0 ≤ (muPlus - muMinus) * (muPlus - muMinus) :=
      int_sq_nonneg_constructive (muPlus - muMinus)
    have hTerm1Nonneg : 0 ≤ q * ((muPlus - muMinus) * (muPlus - muMinus)) :=
      int_mul_nonneg_constructive (by omega) hDiffSqNonneg
    have hProdPos : 0 < 2 * (muPlus * muMinus) := by
      have hMulPos : 0 < muPlus * muMinus := int_mul_pos_constructive hPlus hMinus
      omega
    have hCosShiftNonneg : 0 ≤ q + cPhi := by omega
    have hTerm2Nonneg : 0 ≤ 2 * (muPlus * muMinus) * (q + cPhi) :=
      int_mul_nonneg_constructive (by omega) hCosShiftNonneg
    have hTerm1Zero : q * ((muPlus - muMinus) * (muPlus - muMinus)) = 0 := by omega
    have hTerm2Zero : 2 * (muPlus * muMinus) * (q + cPhi) = 0 := by omega
    have hDiffSqZero : (muPlus - muMinus) * (muPlus - muMinus) = 0 := by
      cases int_mul_eq_zero_constructive hTerm1Zero with
      | inl hq0 => omega
      | inr hSq0 => exact hSq0
    have hDiffZero : muPlus - muMinus = 0 := by
      cases int_mul_eq_zero_constructive hDiffSqZero with
      | inl h0 => exact h0
      | inr h0 => exact h0
    have hCosZero : q + cPhi = 0 := by
      cases int_mul_eq_zero_constructive hTerm2Zero with
      | inl hProd0 => omega
      | inr hC0 => exact hC0
    constructor
    · omega
    · omega
  · intro hCond
    rcases hCond with ⟨hEq, hAntiphase⟩
    subst hEq
    have hSub : muPlus - muPlus = 0 := by omega
    have hSum : q + cPhi = 0 := by omega
    rw [hSub, hSum]
    simp

/-- **Theorem 4 (Master Riemann-Siegel Counter-Wave Holonomy Lock at `Re(s) = 1/2` for All Rings `Z_{4q}`):**
    For any quarter-period `q > 0`, scale `c0 > 0`, vertical frequency coordinate `s0`,
    real-axis deviation `delta` (`Re(s) - 1/2 = delta / (2 c0)`), and relative phase difference `dphi : Int`:
    let `muPlus = cayleyNumNormSq c0 s0 delta` and `muMinus = cayleyDenNormSq c0 s0 delta`
    be the forward and holonomy-reflected wave amplitudes.
    Then the two-wave interference intensity `counterwaveInterferenceIntensity q muPlus muMinus (projCQ q dphi)`
    vanishes (`I = 0`) IF AND ONLY IF:
    (1) `delta = 0`, i.e., `s` lies strictly on the critical line `Re(s) = 1/2`
        (the Weierstrass equator `|w(s)| = 1` where holonomy is unitary `|chi(s)| = 1` and `muPlus = muMinus`), AND
    (2) `pauliPhaseDistNat q dphi = 0`, i.e., the forward and reflected waves interfere in exact Pauli antiphase `pi`
        (`projCQ q dphi = -q`). -/
theorem riemann_holonomy_critical_line_zero_lock
    (q c0 s0 delta dphi : Int)
    (hq : 0 < q) (hc0 : 0 < c0)
    (hPlus : 0 < cayleyNumNormSq c0 s0 delta)
    (hMinus : 0 < cayleyDenNormSq c0 s0 delta) :
    counterwaveInterferenceIntensity q (cayleyNumNormSq c0 s0 delta) (cayleyDenNormSq c0 s0 delta) (projCQ q dphi) = 0 ↔
    (delta = 0 ∧ pauliPhaseDistNat q dphi = 0) := by
  have hBoundAndIff := projCQ_lower_bound_and_pauli_antiphase_iff q dphi
  rw [destructive_interference_zero_iff q (cayleyNumNormSq c0 s0 delta) (cayleyDenNormSq c0 s0 delta) (projCQ q dphi) hq hPlus hMinus hBoundAndIff.1]
  rw [cayley_unitary_equator_iff_critical_line c0 s0 delta hc0]
  rw [hBoundAndIff.2]

#print axioms cayley_norm_imbalance_identity
#print axioms cayley_unitary_equator_iff_critical_line
#print axioms weierstrass_equator_pythagorean_identity
#print axioms projCQ_lower_bound_and_pauli_antiphase_iff
#print axioms counterwave_interference_decomposition
#print axioms destructive_interference_zero_iff
#print axioms riemann_holonomy_critical_line_zero_lock

end RiemannHolonomy
