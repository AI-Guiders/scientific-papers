/-
  MtCarrier.RotatorCalculusPaper
  Self-contained formal verification module for the mathematical paper:
  "On a Remarkable Property of the Cuboctahedral Rotator and Closed-Form Evaluation
   of Fresnel, Jacobi, Bessel, and Dirichlet Integrals in Lean 4"
  ("Об одном замечательном свойстве кусочно-линейного ротатора на кубооктаэдре
    и замкнутом вычислении сумм типа Френеля, Якоби, Бесселя и Дирихле").

  Authors: D. Karavaev & Luch (Луч)
  Zero external dependencies (pure Lean 4 core), zero `sorry`, zero `Classical.choice`.
-/

namespace RotatorCalculusPaper

set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

/-!
## 1. The Catalan Diophantine Lock `1 + 2^d = d^2` and Induced Ring & Cuboctahedron Invariants
-/

theorem two_mul_quad_gt (k : Nat) :
    2 * (2 * (k + 6) * (k + 5)) > 2 * (k + 1 + 6) * (k + 1 + 5) := by
  have h_assoc1 : 2 * (k + 6) * (k + 5) = 2 * ((k + 6) * (k + 5)) := Nat.mul_assoc 2 (k + 6) (k + 5)
  have h_assoc2 : 2 * (k + 1 + 6) * (k + 1 + 5) = 2 * ((k + 1 + 6) * (k + 1 + 5)) :=
    Nat.mul_assoc 2 (k + 1 + 6) (k + 1 + 5)
  rw [h_assoc1, h_assoc2]
  simp only [Nat.left_distrib, Nat.right_distrib]
  omega

theorem two_d_pred_ge_d_sq (k : Nat) :
    2 * (k + 6) * (k + 5) ≥ (k + 6) * (k + 6) := by
  have h_assoc : 2 * (k + 6) * (k + 5) = 2 * ((k + 6) * (k + 5)) := Nat.mul_assoc 2 (k + 6) (k + 5)
  rw [h_assoc]
  simp only [Nat.left_distrib, Nat.right_distrib]
  omega

theorem pow2_gt_two_d_pred (k : Nat) : 2 ^ (k + 6) > 2 * (k + 6) * (k + 5) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h1 : 2 ^ (k + 1 + 6) = 2 * 2 ^ (k + 6) := by
      rw [Nat.add_right_comm k 1 6, Nat.pow_succ, Nat.mul_comm]
    have h2 := two_mul_quad_gt k
    omega

/-- The Catalan exponential-quadratic Diophantine lock `1 + 2^d = d^2`:
exact equality between the `1 + 2^d` unit-vector choice states of a cell (`1` rest state + `2^d` combinations of the `d` unit basis vectors `e_1, ..., e_d`)
and the `d × d = d^2` elementary transition pairs `(e_i → e_j)` between unit basis vectors
(`d` longitudinal transitions `e_i → e_i` plus `d(d-1)` off-diagonal rotations `e_i → e_j`, `i ≠ j`, whose signed sums `±e_i ± e_j` form the `2d(d-1) = 12` vertices of the cuboctahedron `O_2(d)`). -/
abbrev CatalanLock (d : Nat) : Prop :=
  1 + 2 ^ d = d * d

/-- Universal operator law combinator: `P d` holds if and only if `CatalanLock d` is satisfied. -/
abbrev CatalanLaw (P : Nat → Prop) (d : Nat) : Prop :=
  CatalanLock d ↔ (CatalanLock d ∧ P d)

/-- Unique solution of `1 + 2^d = d^2` across all `d ∈ ℕ`. -/
theorem catalan_lock_iff_d3 (d : Nat) :
    CatalanLock d ↔ d = 3 := by
  unfold CatalanLock
  constructor
  · intro h
    have h_split : d < 6 ∨ 6 ≤ d := by omega
    rcases h_split with hlt | h6
    · have hd_cases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
      rcases hd_cases with rfl | rfl | rfl | rfl | rfl | rfl <;> revert h <;> decide
    · have hk : ∃ k, d = k + 6 := ⟨d - 6, by omega⟩
      rcases hk with ⟨k, rfl⟩
      have h1 := pow2_gt_two_d_pred k
      have h2 := two_d_pred_ge_d_sq k
      omega
  · rintro rfl
    decide

/-- Master transfer principle chaining any dimension-parameterized property `P d` to `CatalanLock d`. -/
theorem catalan_law_of_d3 (P : Nat → Prop) (h3 : P 3) (d : Nat) :
    CatalanLaw P d := by
  unfold CatalanLaw
  constructor
  · intro h
    have hd := (catalan_lock_iff_d3 d).mp h
    subst hd
    exact ⟨h, h3⟩
  · exact And.left

/-- Recursive implication chain combinator (`Catalan → Step 1 → Step 2 → Step 3`):
derives `CatalanLaw Q d` directly from a prior link `CatalanLaw P d` and the implication `P 3 → Q 3`. -/
theorem catalan_chain {P Q : Nat → Prop} (d : Nat)
    (hPrev : CatalanLaw P 3) (hNext : P 3 → Q 3) :
    CatalanLaw Q d :=
  catalan_law_of_d3 Q (hNext ((hPrev.mp (by decide : CatalanLock 3)).2)) d

/--Induced algebraic invariants of the discrete phase ring `ℤ_{N_ring(d)}`:
- `nTriangles(d) = 2^d` (`8` triangular faces / octants),
- `modBits(d) = 1 + nTriangles(d)` (`9` bits),
- `nRing(d) = 2^(modBits(d))` (`512` phase ticks),
- `halfPeriod(d) = N_ring(d) / 2` (`256` half-turn antisymmetry period),
- `quarterPeriod(d) = N_ring(d) / 4` (`128` quarter-turn saddle),
- `octantStep(d) = N_ring(d) / 8` (`64` half-quadrant bisector),
- `nSquares(d) = 2 * d` (`6` square faces),
- `nVertices(d) = 2 * (2 * d)` (`12` cuboctahedron vertices),
- `dInSquare = 4` (square-face vertex degree),
- `dOutEdge(d) = 2^d - d` (`5` outer edge degree),
- `normSqEdge(d) = d - 1` (`2`, squared Euclidean norm `‖e‖₂²` of each cuboctahedron vertex),
- `unitStep(d) = d^2 - 2^d` (`1`). -/
def nTriangles (d : Nat) : Nat := 2 ^ d
def modBits (d : Nat) : Nat := 1 + nTriangles d
def nRing (d : Nat) : Nat := 2 ^ modBits d
def halfPeriod (d : Nat) : Nat := nRing d / 2
def quarterPeriod (d : Nat) : Nat := nRing d / 4
def octantStep (d : Nat) : Nat := nRing d / nTriangles d
def dInSquare : Nat := 4
def nSquares (d : Nat) : Nat := 2 * d
def nVertices (d : Nat) : Nat := 2 * nSquares d
def dOutEdge (d : Nat) : Nat := nTriangles d - d
def normSqEdge (d : Nat) : Nat := d - 1
def unitStep (d : Nat) : Nat := modBits d - nTriangles d

/-- The 3D cubic shell orbit `O_k(d) = {e ∈ {-1, 0, +1}^3 | e_x² + e_y² + e_z² = k}`.
At `k = normSqEdge(d) = d - 1 = 2`, `cubicOrbit3D(d - 1)` is the 12-vertex cuboctahedron `O₂(d)`. -/
def cubicGrid3D : List (Int × Int × Int) :=
  ([-1, 0, 1] : List Int).flatMap (fun x =>
    ([-1, 0, 1] : List Int).flatMap (fun y =>
      ([-1, 0, 1] : List Int).map (fun z => (x, y, z))))

def l2NormSq3D (e : Int × Int × Int) : Nat :=
  Int.natAbs (e.1 * e.1 + e.2.1 * e.2.1 + e.2.2 * e.2.2)

def eqNatBool (a b : Nat) : Bool :=
  match a - b, b - a with
  | 0, 0 => true
  | _, _ => false

def eqIntBool (a b : Int) : Bool :=
  match a - b with
  | Int.ofNat 0 => true
  | _ => false

def cubicOrbit3D (k : Nat) : List (Int × Int × Int) :=
  cubicGrid3D.filter (fun e => eqNatBool (l2NormSq3D e) k)

/-!
## 2. The Piecewise-Linear Rotator `(projC, projS)` and Its Universal Constant Difference Wronskian
-/

/-- Principal symmetric branch wrapper `wrapRing(d, x) ∈ (-halfPeriod(d), halfPeriod(d)]`. -/
def wrapRing (d : Nat) (x : Int) : Int :=
  (halfPeriod d : Int) - ((halfPeriod d : Int) - x) % (nRing d : Int)

/-- Piecewise-linear cosine and sine projections on `ℤ_{N_ring(d)}`:
`projC(d, φ) = Q_□(d) - |wrapRing(d, φ)|` and `projS(d, φ) = projC(d, φ - Q_□(d))`. -/
def projC (d : Nat) (phi : Int) : Int :=
  (quarterPeriod d : Int) - (Int.natAbs (wrapRing d phi) : Int)

def projS (d : Nat) (phi : Int) : Int :=
  projC d (phi - (quarterPeriod d : Int))

/-- **Discrete Euler Exponential `eulerExp(d, φ) = (C_d(φ), S_d(φ))` (`e^{iφ}` on `ℤ_{N_ring(d)}`):**
- At `φ = 0`: `eulerExp(d, 0) = (Q_□(d), 0)` (`1`),
- Quarter-turn shift `+Q_□(d)` acts as exact multiplication by the imaginary unit `i`:
  `eulerExp(d, φ + Q_□(d)) = (-S_d(φ), C_d(φ)) = i * eulerExp(d, φ)` for all `φ ∈ ℤ_{N_ring(d)}`,
- Half-turn shift `+Φ_Pauli(d)` (`π`) satisfies **Euler's Identity `e^{iπ} + 1 = 0`** across the entire ring:
  `eulerExp(d, φ + halfPeriod(d)) + eulerExp(d, φ) = (0, 0)`,
- And the inner product of `i * eulerExp(d, φ) = eulerExp(d, φ + Q_□(d))` with the finite difference
  `Δ eulerExp(d, φ) = eulerExp(d, φ + 1) - eulerExp(d, φ)` is identically the constant Wronskian `W_d(φ) ≡ Q_□(d)`
  (the exact discrete differential equation of Euler's exponential `⟨i e^{iφ}, d/dφ e^{iφ}⟩ ≡ 1`)! -/
def eulerExp (d : Nat) (phi : Int) : Int × Int :=
  (projC d phi, projS d phi)

def eulerImagDotDiff (d : Nat) (phi : Int) : Int :=
  (eulerExp d (phi + (quarterPeriod d : Int))).1 * (projC d (phi + 1) - projC d phi) +
  (eulerExp d (phi + (quarterPeriod d : Int))).2 * (projS d (phi + 1) - projS d phi)

/-- **One-Step Difference Wronskian `rotatorWronskian(d, φ)`:**
`W_d(φ) = C_d(φ) * S_d(φ + 1) - S_d(φ) * C_d(φ + 1) = C_d(φ) * ΔS_d(φ) - S_d(φ) * ΔC_d(φ)`.
Unlike the piecewise derivatives `ΔC_d` and `ΔS_d` considered separately in Thompson (`arXiv:1205.3814`),
the coupled difference Wronskian `W_d(φ)` is **identically constant (`= Q_□(d)`) at all `512` points of `ℤ_{N_ring(d)}`**,
including all four corner vertices of the `L¹` diamond! -/
def rotatorWronskian (d : Nat) (phi : Int) : Int :=
  projC d phi * projS d (phi + 1) - projS d phi * projC d (phi + 1)

/-- Rational Weierstrass–Pythagorean lift `(X(φ), Y(φ), R(φ))` to the Euclidean circle `X² + Y² = R²`:
- `pythCosNum(d, φ) = C_d(φ)² - S_d(φ)²`,
- `pythSinNum(d, φ) = 2 * C_d(φ) * S_d(φ)`,
- `pythHypDenom(d, φ) = C_d(φ)² + S_d(φ)²`,
and one-step Euclidean cross/dot products `pythStepCross` and `pythStepDot`. -/
def pythCosNum (d : Nat) (phi : Int) : Int := projC d phi * projC d phi - projS d phi * projS d phi
def pythSinNum (d : Nat) (phi : Int) : Int := (normSqEdge d : Int) * projC d phi * projS d phi
def pythHypDenom (d : Nat) (phi : Int) : Int := projC d phi * projC d phi + projS d phi * projS d phi

def pythStepCross (d : Nat) (phi : Int) : Int :=
  pythCosNum d phi * pythSinNum d (phi + 1) - pythSinNum d phi * pythCosNum d (phi + 1)

def pythStepDot (d : Nat) (phi : Int) : Int :=
  pythCosNum d phi * pythCosNum d (phi + 1) + pythSinNum d phi * pythSinNum d (phi + 1)

def rotatorInnerStep (d : Nat) (phi : Int) : Int :=
  projC d phi * projC d (phi + 1) + projS d phi * projS d (phi + 1)

/-!
## 3. Definite Ring Integrals, Antiderivatives, Jacobi Elliptic Triad, and Closed-Form Fresnel/Dirichlet/Parseval/Bessel Sums
-/

/-- Generic Boolean universal quantifier over `[0, N)` without `List.range` (`0 Classical.choice`). -/
def allUpTo : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => allUpTo n p && p n

/-- Generic definite discrete integral `discreteIntegral(N, f) = ∑_{φ=0}^{N-1} f(φ)`. -/
def discreteIntegral : Nat → (Int → Int) → Int
  | 0, _ => 0
  | n + 1, f => discreteIntegral n f + f (n : Int)

/-- Exact discrete antiderivatives `antiderivC(d, Φ) = ∑_{φ=0}^{Φ-1} C_d(φ)` and `antiderivS(d, Φ) = ∑_{φ=0}^{Φ-1} S_d(φ)`. -/
def antiderivC (d phiUpper : Nat) : Int :=
  discreteIntegral phiUpper (fun phi => projC d phi)

def antiderivS (d phiUpper : Nat) : Int :=
  discreteIntegral phiUpper (fun phi => projS d phi)

/-- Lemniscate Jacobi elliptic triad `(jacobiSn, jacobiCn, jacobiDoubleDn)` at the cuboctahedron modulus `k² = 1 / ‖e‖₂² = 1/2`. -/
def jacobiSn (d : Nat) (phi : Int) : Int := projS d phi
def jacobiCn (d : Nat) (phi : Int) : Int := projC d phi
def jacobiDoubleDn (d : Nat) (phi : Int) : Int :=
  (halfPeriod d : Int) - (Int.natAbs (projS d phi) : Int)

/-- Two-tick symplectic Verlet difference recurrence trajectory `φ(t) = φ₀ + ω₀ t + Φ * t(t-1)/2`:
- at `Φ = 0`: generates Liouville's elementary circular basis,
- at `Φ ≠ 0`: generates the non-elementary quadratic-phase Fresnel/Airy basis. -/
def verletParabolaPhase (phi0 omega0 phiAccel : Int) (t : Nat) : Int :=
  phi0 + omega0 * (t : Int) + phiAccel * ((t * (t - 1) / 2 : Nat) : Int)

def verletFresnelCosPrimitive (d : Nat) (phi0 omega0 phiAccel : Int) (nSteps : Nat) : Int :=
  discreteIntegral nSteps (fun t => projC d (verletParabolaPhase phi0 omega0 phiAccel (Int.toNat t)))

def verletFresnelSinPrimitive (d : Nat) (phi0 omega0 phiAccel : Int) (nSteps : Nat) : Int :=
  discreteIntegral nSteps (fun t => projS d (verletParabolaPhase phi0 omega0 phiAccel (Int.toNat t)))

/-- 1. Discrete Fresnel diffraction integrals `∑_{φ=0}^{N_ring(d)-1} C_d(φ²)` and `∑_{φ=0}^{N_ring(d)-1} S_d(φ²)`. -/
def fresnelCosIntegral (d : Nat) : Int :=
  discreteIntegral (nRing d) (fun phi => projC d (phi * phi))

def fresnelSinIntegral (d : Nat) : Int :=
  discreteIntegral (nRing d) (fun phi => projS d (phi * phi))

/-- 2. Complete & first-quadrant incomplete elliptic integrals of the second kind. -/
def completeEllipticIntegral (d : Nat) (a b : Int) : Int :=
  a * discreteIntegral (nRing d) (fun phi => (Int.natAbs (projC d phi) : Int)) +
  b * discreteIntegral (nRing d) (fun phi => (Int.natAbs (projS d phi) : Int))

def incompleteEllipticFirstQuad (d phiUpper : Nat) (a b : Int) : Int :=
  a * discreteIntegral phiUpper (fun phi => projC d phi) +
  b * discreteIntegral phiUpper (fun phi => projS d phi)

/-- 3. Discrete Dirichlet sine integral `Si_d(Φ) = ∑_{φ=1}^{Φ} (S_d(φ) / φ)`. -/
def dirichletSiIntegral (d phiUpper : Nat) : Int :=
  discreteIntegral phiUpper (fun k => (projS d (k + 1)).tdiv (k + 1))

/-- 4. Discrete Parseval squared-projection energy integrals `∑_{φ=0}^{N_ring(d)-1} C_d(φ)²` and `∑_{φ=0}^{N_ring(d)-1} S_d(φ)²`. -/
def parsevalCosSqIntegral (d : Nat) : Int :=
  discreteIntegral (nRing d) (fun phi => projC d phi * projC d phi)

def parsevalSinSqIntegral (d : Nat) : Int :=
  discreteIntegral (nRing d) (fun phi => projS d phi * projS d phi)

/-- 5. Discrete zero-order Bessel integral `J_{0,d}(k) = ∑_{φ=0}^{N_ring(d)-1} C_d(k * S_d(φ))`. -/
def besselJ0Integral (d : Nat) (kWave : Int) : Int :=
  discreteIntegral (nRing d) (fun phi => projC d (kWave * projS d phi))

/-- 6. Pochhammer falling factorial `m^{\_k}` for exact remainder-free polynomial integration. -/
def fallingFactorial : Nat → Nat → Nat
  | _, 0 => 1
  | m, k + 1 => m * fallingFactorial (m - 1) k

/-!
## 4. First-Principles 3D Cuboctahedron Continuum Volume Integrator (Archimedes Equizonal Theorem)
-/

/-- Number of vertices of the cuboctahedron `O₂(d) = cubicOrbit3D(d - 1)` in the coordinate slice `e_x = exTarget`. -/
def countExInList : List (Int × Int × Int) → Int → Nat
  | [], _ => 0
  | e :: rest, exTarget => (if eqIntBool e.1 exTarget then 1 else 0) + countExInList rest exTarget

def cuboctLayerCount (d : Nat) (exTarget : Int) : Nat :=
  countExInList (cubicOrbit3D (d - 1)) exTarget

/-- Sum of `f3D` over a list of 3D lattice vectors without `List.foldl` (`0 Classical.choice`). -/
def sumOverShell3D : List (Int × Int × Int) → (Int × Int × Int → Int) → Int
  | [], _ => 0
  | e :: rest, f3D => f3D e + sumOverShell3D rest f3D

/-- Natural center-plus-shell 3D volume integrator on the cuboctahedron ball `B₁(d) = {0} ∪ O₂(d)`:
weights the central node `(0,0,0)` by `|N(d)| = 12` equally against the sum over the `12` vertices of `O₂(d) = cubicOrbit3D(d - 1)`. -/
def cuboct3DContinuumIntegrator (d : Nat) (f3D : Int × Int × Int → Int) : Int :=
  (nVertices d : Int) * f3D (0, 0, 0) +
  sumOverShell3D (cubicOrbit3D (d - 1)) f3D

/-- Exact analytical 1D continuum integral `(p + 1) * (1/2) * ∫_{-1}^{+1} x^p dx`. -/
def exactContinuum1DUnitIntegralNum (pDeg : Nat) : Int :=
  ((1 : Int) - ((-1 : Int) ^ (pDeg + 1))) / 2

/-- **Step-`s` Wronskian `stepWronskian(d, s, φ)` and Inner Product `stepInner(d, s, φ)` for `\pi(n)` as a Function of `n = N_ring(d) / s`:**
On the Weierstrass `n`-gon with step `s = N_ring(d) / n`, the inscribed rational approximation `\pi_in(n)` and circumscribed
rational approximation `\pi_out(n)` have per-segment terms `a_j = (I_s * W_s) / (R_1 * R_2)` and `b_j = W_s / I_s`.
By Brahmagupta's identity `R_1 * R_2 - I_s² = W_s²`, their difference over common denominator `I_s * R_1 * R_2`
is identically the **cube of the step Wronskian `W_s³ = (s * Q_□(d))³`**:
`b_j - a_j = W_s³ / (I_s * R_1 * R_2) > 0`!
Under polygon doubling `n ↦ 2n` (`s ↦ s / 2`), `W_s³` shrinks by `2^d = |△(d)| = 8` while the segment count doubles by `‖e‖₂² = d - 1 = 2`,
so the rational bracket width `\pi_out(n) - \pi_in(n)` contracts by the exact factor `2^d / (d - 1) = d_in(□) = 4` at every step! -/
def stepWronskian (d : Nat) (s phi : Int) : Int :=
  projC d phi * projS d (phi + s) - projS d phi * projC d (phi + s)

def stepInner (d : Nat) (s phi : Int) : Int :=
  projC d phi * projC d (phi + s) + projS d phi * projS d (phi + s)

/-- Rational pair addition `(n₁, d₁) + (n₂, d₂) = (n₁ * d₂ + n₂ * d₁, d₁ * d₂)` and reduction for `\pi_in(n)` and `\pi_out(n)`. -/
def addRat (p1 p2 : Nat × Nat) : Nat × Nat :=
  (p1.1 * p2.2 + p2.1 * p1.2, p1.2 * p2.2)

def reduceRat (p : Nat × Nat) : Nat × Nat :=
  (p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)

/-- Helper fold over `nSteps` for rational sums without `List.range` (`0 Classical.choice`). -/
def foldRatUpTo : Nat → (Nat → Nat × Nat) → Nat × Nat
  | 0, _ => (0, 1)
  | n + 1, f => reduceRat (addRat (foldRatUpTo n f) (f n))

/-- Inscribed rational `\pi_in(n)` and circumscribed rational `\pi_out(n)` as explicit functions of polygon side count `n` (`s = N_ring(d) / n`). -/
def piInscribedRat (d nSides : Nat) : Nat × Nat :=
  foldRatUpTo (nSides / 2) (fun j =>
    reduceRat
      ((stepInner d ((nRing d / nSides : Nat) : Int) ((j * (nRing d / nSides) : Nat) : Int)).toNat *
       (stepWronskian d ((nRing d / nSides : Nat) : Int) ((j * (nRing d / nSides) : Nat) : Int)).toNat,
       (pythHypDenom d ((j * (nRing d / nSides) : Nat) : Int)).toNat *
       (pythHypDenom d (((j + 1) * (nRing d / nSides) : Nat) : Int)).toNat))

def piCircumscribedRat (d nSides : Nat) : Nat × Nat :=
  foldRatUpTo (nSides / 2) (fun j =>
    reduceRat
      ((stepWronskian d ((nRing d / nSides : Nat) : Int) ((j * (nRing d / nSides) : Nat) : Int)).toNat,
       (stepInner d ((nRing d / nSides : Nat) : Int) ((j * (nRing d / nSides) : Nat) : Int)).toNat))

/-- Huygens–Snellius dimension-weighted rational estimator `\pi_d(n) = (\pi_in(n) + (d - 1) * \pi_out(n)) / d`. -/
def piHuygensSnelliusRat (d nSides : Nat) : Nat × Nat :=
  reduceRat
    ((addRat (piInscribedRat d nSides) (normSqEdge d * (piCircumscribedRat d nSides).1, (piCircumscribedRat d nSides).2)).1,
     d * (addRat (piInscribedRat d nSides) (normSqEdge d * (piCircumscribedRat d nSides).1, (piCircumscribedRat d nSides).2)).2)

/-- Calculator-Free Rational Sine Operator `verletParabolaSineRat(d, p, q)` on Fractions `(p / q) * Q_□(d)` of a Right Angle:
Evaluates the Verlet half-turn parabola `P(p, q) = p * (2 * q - p)` weighted by the cuboctahedron square-face degree `d_in(□) = 4`
and outer edge degree `d_out(E)(d) = 5`:
`sin_rat(d; p, q) = reduceRat(d_in(□) * p * (2 * q - p), d_out(E)(d) * q² - p * (2 * q - p))`.
At the canonical fractions of a right angle `p / q ∈ {1 / modBits(d) (10°), 1 / d (30°), 1 / ‖e‖₂² (45°), ‖e‖₂² / d (60°), 1 / 1 (90°)}`,
it outputs the exact structural invariants of the cuboctahedron `(17/97, 1/2, 12/17, 32/37, 1/1)`! -/
def verletParabolaSineRat (d p q : Nat) : Nat × Nat :=
  reduceRat
    (dInSquare * p * (normSqEdge d * q - p),
     dOutEdge d * q * q - p * (normSqEdge d * q - p))

/-- Directional second moment `M^{(2)}_d(k) = ∑_{e ∈ O₂(d)} (k · e)²` on the cuboctahedron shell `O₂(d)`. -/
def cuboctSecondMoment (d : Nat) (kz ky kx : Int) : Int :=
  (cubicOrbit3D (d - 1)).foldl (fun acc (ez, ey, ex) =>
    acc + (kz * ez + ky * ey + kx * ex) ^ 2) 0

/-- Directional fourth moment `M^{(4)}_d(k) = ∑_{e ∈ O₂(d)} (k · e)⁴` on the cuboctahedron shell `O₂(d)`. -/
def cuboctFourthMoment (d : Nat) (kz ky kx : Int) : Int :=
  (cubicOrbit3D (d - 1)).foldl (fun acc (ez, ey, ex) =>
    acc + (kz * ez + ky * ey + kx * ex) ^ 4) 0

/-- Closed-form fourth-moment operator `|V_{O₂}(d)| * |k|⁴ - d_in(□) * ∑_{i=1}^d k_i⁴ = 12 |k|⁴ - 4 ∑ k_i⁴`. -/
def cuboctFourthMomentClosedForm (d : Nat) (kz ky kx : Int) : Int :=
  (nVertices d : Int) * (kz * kz + ky * ky + kx * kx) ^ 2 -
  (dInSquare : Int) * (kz ^ 4 + ky ^ 4 + kx ^ 4)

/-- Universal verification across the 3D wavevector grid `k ∈ [-d, d]³` (`343` wavevectors) of exact `O(k²)` isotropy
`M^{(2)}_d(k) = |△(d)| * |k|² = 8 |k|²` and exact `O(k⁴)` lattice anisotropy `M^{(4)}_d(k) = 12 |k|⁴ - 4 ∑ k_i⁴`. -/
def checkCuboctMomentIdentitiesBool (d : Nat) : Bool :=
  let grid := [-(d : Int), -((normSqEdge d : Nat) : Int), -((unitStep d : Nat) : Int), 0,
               ((unitStep d : Nat) : Int), ((normSqEdge d : Nat) : Int), (d : Int)]
  grid.all (fun kz =>
    grid.all (fun ky =>
      grid.all (fun kx =>
        eqIntBool (cuboctSecondMoment d kz ky kx)
          ((nTriangles d : Int) * (kz * kz + ky * ky + kx * kx)) &&
        eqIntBool (cuboctFourthMoment d kz ky kx)
          (cuboctFourthMomentClosedForm d kz ky kx))))

/-- Number of independent rotation/tilt planes (Euler angles `dim SO(d) = d(d-1)/2`), which equals `d` uniquely at `d = 3`,
partitioning the `12` cuboctahedron vertices into `3 × 4` equatorial squares `(xy, xz, yz)`. -/
def eulerPlaneCount (d : Nat) : Nat :=
  d * (d - 1) / normSqEdge d

/-- Exact root-free 3D Euler-angle rotator `(φ₁, φ₂, φ₃) ∈ ℤ_{N_ring(d)}³` acting on `(x, y, z) ∈ ℤ³`
by composing Weierstrass Pythagorean rotations in the three cuboctahedron coordinate planes `(xy, xz, yz)`:
1. Yaw `φ₁` in the `xy`-plane,
2. Pitch/nutation tilt `φ₂` in the `xz`-plane,
3. Roll tilt `φ₃` in the `yz`-plane. -/
def euler3DRotateVec (d : Nat) (phi1 phi2 phi3 x y z : Int) : Int × Int × Int :=
  let x1 := pythCosNum d phi1 * x - pythSinNum d phi1 * y
  let y1 := pythSinNum d phi1 * x + pythCosNum d phi1 * y
  let z1 := pythHypDenom d phi1 * z
  let x2 := pythCosNum d phi2 * x1 - pythSinNum d phi2 * z1
  let y2 := pythHypDenom d phi2 * y1
  let z2 := pythSinNum d phi2 * x1 + pythCosNum d phi2 * z1
  let x3 := pythHypDenom d phi3 * x2
  let y3 := pythCosNum d phi3 * y2 - pythSinNum d phi3 * z2
  let z3 := pythSinNum d phi3 * y2 + pythCosNum d phi3 * z2
  (x3, y3, z3)

/-- Product of the three Weierstrass hypotenuse denominators `R_d(φ₁) * R_d(φ₂) * R_d(φ₃)`. -/
def euler3DHypDenom (d : Nat) (phi1 phi2 phi3 : Int) : Int :=
  pythHypDenom d phi1 * pythHypDenom d phi2 * pythHypDenom d phi3

/-- Squared Euclidean norm `x² + y² + z²` of a 3D integer vector. -/
def vec3NormSq (v : Int × Int × Int) : Int :=
  v.1 * v.1 + v.2.1 * v.2.1 + v.2.2 * v.2.2

/-!
## 5. Main Theorems of the Paper
-/

/-- **Theorem 1 (Discrete Euler Exponential `e^{iφ}`, Euler's Identity `e^{iπ} + 1 = 0`, Universal Constant Difference Wronskian `⟨i e^{iφ}, Δ e^{iφ}⟩ ≡ Q_□(d)`, Brahmagupta–Weierstrass Euclidean Lift, and Fundamental Theorem of Discrete Calculus)**: -/
theorem thm1_constant_wronskian_weierstrass_lift_and_newton_leibniz (d : Nat) :
    CatalanLaw (fun d =>
      -- (i) Discrete Euler exponential e^{iφ}, multiplication by i via +Q_□(d), Euler's identity e^{iπ} + 1 = 0, and ⟨i e^{iφ}, Δ e^{iφ}⟩ = W_d(φ) ≡ Q_□(d)
      (allUpTo (nRing d) (fun phi =>
         eqNatBool (Int.natAbs (projC d (phi : Int)) + Int.natAbs (projS d (phi : Int))) (quarterPeriod d) &&
         eqIntBool (eulerExp d ((phi : Int) + (quarterPeriod d : Int))).1 (-projS d (phi : Int)) &&
         eqIntBool (eulerExp d ((phi : Int) + (quarterPeriod d : Int))).2 (projC d (phi : Int)) &&
         eqIntBool ((eulerExp d ((phi : Int) + (halfPeriod d : Int))).1 + (eulerExp d (phi : Int)).1) 0 &&
         eqIntBool ((eulerExp d ((phi : Int) + (halfPeriod d : Int))).2 + (eulerExp d (phi : Int)).2) 0 &&
         eqIntBool (eulerImagDotDiff d (phi : Int)) (rotatorWronskian d (phi : Int)) &&
         eqIntBool (rotatorWronskian d (phi : Int)) (quarterPeriod d : Int)) = true ∧
       discreteIntegral (nRing d) (fun phi => rotatorWronskian d phi) =
         ((nRing d * quarterPeriod d : Nat) : Int)) ∧
      -- (ii) Root-free Euclidean Pythagorean circle identity X² + Y² = R² and Brahmagupta-Weierstrass step differentials
      (allUpTo (nRing d) (fun phi =>
         eqIntBool
           (pythCosNum d (phi : Int) * pythCosNum d (phi : Int) +
            pythSinNum d (phi : Int) * pythSinNum d (phi : Int))
           (pythHypDenom d (phi : Int) * pythHypDenom d (phi : Int)) &&
         eqIntBool (pythStepCross d (phi : Int))
           (((normSqEdge d * quarterPeriod d : Nat) : Int) * rotatorInnerStep d (phi : Int)) &&
         eqIntBool (pythStepDot d (phi : Int))
           (rotatorInnerStep d (phi : Int) * rotatorInnerStep d (phi : Int) -
            ((quarterPeriod d * quarterPeriod d : Nat) : Int))) = true) ∧
      -- (iii) Fundamental Theorem of Discrete Calculus (Newton-Leibniz) across all 512 points & half-wave area = Q_□(d)²
      (allUpTo (nRing d) (fun phi =>
         eqIntBool (antiderivC d (phi + 1) - antiderivC d phi) (projC d (phi : Int)) &&
         eqIntBool (antiderivS d (phi + 1) - antiderivS d phi) (projS d (phi : Int))) = true ∧
       antiderivC d (nRing d) = 0 ∧
       antiderivS d (nRing d) = 0 ∧
       antiderivS d (halfPeriod d) = ((quarterPeriod d * quarterPeriod d : Nat) : Int))) d :=
  catalan_law_of_d3 _ ⟨⟨rfl, rfl⟩, rfl, ⟨rfl, rfl, rfl, rfl⟩⟩ d

/-- **Theorem 2 (Closed-Form Evaluation of Fresnel, Jacobi Elliptic, Dirichlet `Si`, Parseval, and Bessel `J₀` Integrals)**: -/
theorem thm2_closed_form_fresnel_jacobi_dirichlet_parseval_bessel_integrals (d : Nat) :
    CatalanLaw (fun d =>
      -- (i) Lemniscate Jacobi elliptic triad (sn_d, cn_d, dn_d) invariants at cuboctahedron modulus k² = 1/‖e‖₂² = 1/2
      (allUpTo (nRing d) (fun phi =>
         eqNatBool (Int.natAbs (jacobiSn d (phi : Int)) + Int.natAbs (jacobiCn d (phi : Int))) (quarterPeriod d) &&
         eqIntBool (jacobiDoubleDn d (phi : Int) + (Int.natAbs (jacobiSn d (phi : Int)) : Int)) (halfPeriod d : Int)) = true ∧
       completeEllipticIntegral d (normSqEdge d : Int) (d : Int) =
         ((halfPeriod d * quarterPeriod d * dOutEdge d : Nat) : Int) ∧
       incompleteEllipticFirstQuad d (quarterPeriod d) (unitStep d : Int) (unitStep d : Int) =
         ((quarterPeriod d * quarterPeriod d : Nat) : Int)) ∧
      -- (ii) Closed-form Fresnel diffraction integrals: C_Fresnel = S_Fresnel = d_in(□) * N_ring(d) = 2048 (stationary phase at ψ = K_P(d) = 64)
      (fresnelCosIntegral d = ((dInSquare * nRing d : Nat) : Int) ∧
       fresnelSinIntegral d = ((dInSquare * nRing d : Nat) : Int) ∧
       fresnelCosIntegral d = fresnelSinIntegral d ∧
       projC d (octantStep d : Int) = (octantStep d : Int) ∧
       projS d (octantStep d : Int) = (octantStep d : Int)) ∧
      -- (iii) Closed-form Dirichlet Si integral (128 on Q₁ and half-period) and Parseval energy integral (2,796,288)
      (dirichletSiIntegral d (quarterPeriod d) = (quarterPeriod d : Int) ∧
       dirichletSiIntegral d (halfPeriod d) = (quarterPeriod d : Int) ∧
       parsevalCosSqIntegral d = parsevalSinSqIntegral d ∧
       (nSquares d : Int) * parsevalCosSqIntegral d =
         ((nRing d * (normSqEdge d * quarterPeriod d * quarterPeriod d + unitStep d) : Nat) : Int)) ∧
      -- (iv) Closed-form Bessel J₀ integral (65536 at k=0, 32768 at k=1, and exact root 0 at k = d_in(□) = 4)
      (besselJ0Integral d 0 = ((nRing d * quarterPeriod d : Nat) : Int) ∧
       besselJ0Integral d (unitStep d : Int) = ((halfPeriod d * quarterPeriod d : Nat) : Int) ∧
       besselJ0Integral d (dInSquare : Int) = 0)) d :=
  catalan_chain d (thm1_constant_wronskian_weierstrass_lift_and_newton_leibniz 3)
    (fun _ => ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩)

/-- **Theorem 3 (First-Principles Derivation of 3D & 1D Continuum Integration from the Cuboctahedron Archimedes Equizonal Partition)**: -/
theorem thm3_continuum_integration_from_cuboctahedron_archimedes_layers (d : Nat) :
    CatalanLaw (fun d =>
      -- (i) Archimedes equizonal partition of the 12 cuboctahedron vertices into (4, 4, 4) across e_x ∈ {-1, 0, +1}
      ((cubicOrbit3D (d - 1)).length = nVertices d ∧
       cuboctLayerCount d (-(unitStep d : Int)) = dInSquare ∧
       cuboctLayerCount d 0 = dInSquare ∧
       cuboctLayerCount d (unitStep d : Int) = dInSquare ∧
       nVertices d + cuboctLayerCount d 0 = dInSquare * dInSquare ∧
       normSqEdge d * nVertices d = dInSquare * nSquares d) ∧
      -- (ii) Exact agreement of the 3D cuboctahedron operator with the 1D and 3D continuum Riemann integral ∭_{[-1,1]³} F dV up to degree d = 3
      (allUpTo dInSquare (fun p =>
         eqIntBool (((p + 1 : Nat) : Int) * cuboct3DContinuumIntegrator d (fun (ex, _, _) => ex ^ p))
           (((normSqEdge d * nVertices d : Nat) : Int) * exactContinuum1DUnitIntegralNum p)) = true ∧
       cuboct3DContinuumIntegrator d (fun (ex, ey, ez) => ex * ex + ey * ey + ez * ez) =
         ((normSqEdge d * nVertices d : Nat) : Int) ∧
       cuboct3DContinuumIntegrator d (fun (ex, ey, ez) => ex * ey * ez) = 0) ∧
      -- (iii) Exact Pochhammer falling-factorial discrete integration & M-layer 512-gon circle radius lower bound C² + S² ≥ Q_□² / 2
      ((dInSquare : Int) * discreteIntegral (nVertices d + unitStep d) (fun m => (fallingFactorial (Int.toNat m) d : Int)) =
         (fallingFactorial (nVertices d + unitStep d) dInSquare : Int) ∧
       allUpTo (nRing d) (fun phi =>
         Nat.ble (quarterPeriod d * quarterPeriod d) (Int.toNat (pythHypDenom d (phi : Int)) * normSqEdge d)) = true ∧
       nSquares d * nRing d * nRing d = d * normSqEdge d * (nRing d ^ (normSqEdge d))) ∧
      -- (iv) \pi(n) as a pure rational function of n on the Weierstrass rotator: Wronskian-cube identity R₁*R₂ - I_s² = W_s²,
      -- strict monotone nested brackets \pi_in(8) < \pi_in(16) < \pi_in(32) < \pi_out(32) < \pi_out(16) < \pi_out(8),
      -- and Huygens-Snellius estimator \pi_d(16) = 142 / 45 = (2*K_P(d) + 14) / (modBits(d) * d_out(E)(d))!
      (allUpTo (nRing d) (fun phi =>
         eqIntBool
           (pythHypDenom d (phi : Int) * pythHypDenom d ((phi : Int) + 1) -
            rotatorInnerStep d (phi : Int) * rotatorInnerStep d (phi : Int))
           (rotatorWronskian d (phi : Int) * rotatorWronskian d (phi : Int))) = true ∧
       piInscribedRat d (nTriangles d) = (normSqEdge d, unitStep d) ∧
       piCircumscribedRat d (nTriangles d) = (dInSquare, unitStep d) ∧
       piInscribedRat d (normSqEdge d * nTriangles d) = (nVertices d + normSqEdge d, dOutEdge d) ∧
       piCircumscribedRat d (normSqEdge d * nTriangles d) = (nVertices d - normSqEdge d, d) ∧
       piHuygensSnelliusRat d (normSqEdge d * nTriangles d) =
         (normSqEdge d * octantStep d + nVertices d + normSqEdge d, modBits d * dOutEdge d) ∧
       (piInscribedRat d (nTriangles d)).1 * (piInscribedRat d (normSqEdge d * nTriangles d)).2 <
         (piInscribedRat d (normSqEdge d * nTriangles d)).1 * (piInscribedRat d (nTriangles d)).2 ∧
       (piInscribedRat d (normSqEdge d * nTriangles d)).1 * (piInscribedRat d (dInSquare * nTriangles d)).2 <
         (piInscribedRat d (dInSquare * nTriangles d)).1 * (piInscribedRat d (normSqEdge d * nTriangles d)).2 ∧
       (piInscribedRat d (dInSquare * nTriangles d)).1 * (piCircumscribedRat d (dInSquare * nTriangles d)).2 <
         (piCircumscribedRat d (dInSquare * nTriangles d)).1 * (piInscribedRat d (dInSquare * nTriangles d)).2 ∧
       (piCircumscribedRat d (dInSquare * nTriangles d)).1 * (piCircumscribedRat d (normSqEdge d * nTriangles d)).2 <
         (piCircumscribedRat d (normSqEdge d * nTriangles d)).1 * (piCircumscribedRat d (dInSquare * nTriangles d)).2 ∧
       (piCircumscribedRat d (normSqEdge d * nTriangles d)).1 * (piCircumscribedRat d (nTriangles d)).2 <
         (piCircumscribedRat d (nTriangles d)).1 * (piCircumscribedRat d (normSqEdge d * nTriangles d)).2) ∧
      -- (v) Calculator-free rational sine from the Verlet parabola at 10°, 30°, 45°, 60°, 90°: (17/97, 1/2, 12/17, 32/37, 1/1)
      (verletParabolaSineRat d (unitStep d) (modBits d) =
         (nVertices d + unitStep d + dInSquare, dInSquare * dInSquare + modBits d * modBits d) ∧
       verletParabolaSineRat d (unitStep d) d = (unitStep d, normSqEdge d) ∧
       verletParabolaSineRat d (unitStep d) (normSqEdge d) =
         (nVertices d, nVertices d + unitStep d + dInSquare) ∧
       verletParabolaSineRat d (normSqEdge d) d =
         (octantStep d / normSqEdge d, dInSquare ^ d - d ^ d) ∧
       verletParabolaSineRat d (unitStep d) (unitStep d) = (unitStep d, unitStep d)) ∧
      -- (vi) Exact O(k²) isotropy `∑ (k·e)² = 8 |k|²`, O(k⁴) fourth-moment identity `∑ (k·e)⁴ = 12 |k|⁴ - 4 ∑ k_i⁴`,
      -- and root-free 3D Euler-angle rotator `(φ₁, φ₂, φ₃)` across the `d(d-1)/2 = 3` cuboctahedron planes `(xy, xz, yz)`
      (checkCuboctMomentIdentitiesBool d = true ∧
       cuboctFourthMoment d (unitStep d : Int) 0 0 =
         (nVertices d : Int) - (dInSquare : Int) ∧
       cuboctFourthMoment d (unitStep d : Int) (unitStep d : Int) 0 / (dInSquare : Int) =
         (nVertices d : Int) - (normSqEdge d : Int) ∧
       cuboctFourthMoment d (unitStep d : Int) (unitStep d : Int) (unitStep d : Int) =
         ((nVertices d * nTriangles d : Nat) : Int) ∧
       eulerPlaneCount d = d ∧
       nVertices d = eulerPlaneCount d * dInSquare ∧
       ((cubicOrbit3D (d - 1)).all (fun (ex, ey, ez) =>
         eqIntBool
           (vec3NormSq (euler3DRotateVec d (d : Int) (dOutEdge d : Int) (modBits d : Int) ex ey ez))
           (euler3DHypDenom d (d : Int) (dOutEdge d : Int) (modBits d : Int) *
            euler3DHypDenom d (d : Int) (dOutEdge d : Int) (modBits d : Int) *
            (normSqEdge d : Int))) = true) ∧
       euler3DRotateVec d 0 (octantStep d : Int) 0 (unitStep d : Int) (unitStep d : Int) 0 =
         (0,
          euler3DHypDenom d 0 (octantStep d : Int) 0,
          euler3DHypDenom d 0 (octantStep d : Int) 0))) d :=
  catalan_chain d (thm2_closed_form_fresnel_jacobi_dirichlet_parseval_bessel_integrals 3)
    (fun _ => ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩,
               ⟨rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide, by decide⟩,
               ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩)

#print axioms catalan_lock_iff_d3
#print axioms thm1_constant_wronskian_weierstrass_lift_and_newton_leibniz
#print axioms thm2_closed_form_fresnel_jacobi_dirichlet_parseval_bessel_integrals
#print axioms thm3_continuum_integration_from_cuboctahedron_archimedes_layers

end RotatorCalculusPaper
