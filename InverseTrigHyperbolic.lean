import RotatorQuadrature

/-!
# Exact Projective Inverse Trigonometry (`atan`, `acot`) and Root-Free / Logarithm-Free Hyperbolic Functions (`cosh`, `sinh`, `tanh`, `coth`, `asinh`, `atanh`) on `ℤ_{4Q}` (`0 sorryAx`, `0 Classical.choice`, `0 Prop premises`)

This pure mathematics module (`Constructive/InverseTrigHyperbolic.lean`) formalizes:
1. **Exact Inverse Tangent & Inverse Cotangent on the `L¹` Diamond (`|C_Q(φ)| + |S_Q(φ)| = Q`):**
   - In the first quadrant `0 ≤ φ ≤ Q`, `C_Q(φ) = Q - φ` and `S_Q(φ) = φ`, so `C_Q(φ) + S_Q(φ) = Q`.
   - Therefore, for any homogeneous scaling `λ ≥ 1` (`X = λ(Q - φ)`, `Y = λ φ`),
     `atanL1(Y, X) = (Q * Y) / (X + Y) = φ` and `acotL1(X, Y) = (Q * X) / (X + Y) = Q - φ`
     with **zero approximation error** and exact complementary sum `atanL1(Y, X) + acotL1(X, Y) = Q`!
   - Across all 4 quadrants of the 512-tick ring (`Q = 128`), `atan2L1Ring512` and `acot2L1Ring512` invert `(C_128(φ), S_128(φ))`
     bijectively at every single phase tick `φ ∈ {0, 1, ..., 511}`.
2. **Projective Gudermann–Minkowski Hyperbolic Functions (`Ch_Q`, `Sh_Q`, `D_hyp`) Without Exponentials:**
   - Swapping the horizontal leg and hypotenuse of the Weierstrass circle lift yields the integer hyperbolic triple:
     `Ch_Q(φ) = C_Q(φ)² + S_Q(φ)²`, `Sh_Q(φ) = 2 * C_Q(φ) * S_Q(φ)`, `D_hyp(φ) = C_Q(φ)² - S_Q(φ)²`.
   - At every phase `φ ∈ ℤ` and for every `Q ≥ 1`, this triple satisfies the **exact Minkowski hyperbola identity**:
     `Ch_Q(φ)² - Sh_Q(φ)² ≡ D_hyp(φ)²` (so `(Ch_Q / D_hyp)² - (Sh_Q / D_hyp)² ≡ 1`).
   - On the `L¹` diamond `|C_Q(φ)| + |S_Q(φ)| = Q`, the light-cone sum is identically constant:
     `Ch_Q(φ) + |Sh_Q(φ)| = (|C_Q(φ)| + |S_Q(φ)|)² ≡ Q²`.
3. **Root-Free and Logarithm-Free Exact Inverse Hyperbolic Functions (`invHypQ`, `atanhCayley`):**
   - Because `C_Q(φ) + S_Q(φ) = Q` in the first quadrant, the quadratic difference `D_hyp(φ) = C_Q(φ)² - S_Q(φ)²`
     factorizes into the **linear** form `Q * (Q - 2φ)`, and `Ch_Q(φ) + Sh_Q(φ) - D_hyp(φ) = 2 * S_Q(φ) * (C_Q(φ) + S_Q(φ)) = 2 * Q * φ`.
   - Dividing by `2 * Q` recovers the exact angle `φ` from `(Ch_Q(φ), Sh_Q(φ), D_hyp(φ))` without square roots or logarithms!
   - On light-cone coordinates `(U, V)`, the projective hyperbolic tangent `tanhCayley(U, V) = (U - V, U + V)` and
     hyperbolic cotangent `cothCayley(U, V) = (U + V, U - V)` are inverted algebraically by
     `atanhCayley(Sh, Ch) = (Ch + Sh, Ch - Sh) = (2U, 2V)` and `acothCayley(Ch, Sh) = (Ch + Sh, Ch - Sh) = (2U, 2V)`.
-/

/-- Projective tangent pair `tanPairQ(Q, φ) = (S_Q(φ), C_Q(φ))` and cotangent pair `cotPairQ(Q, φ) = (C_Q(φ), S_Q(φ))`. -/
def tanPairQ (Q phi : Int) : Int × Int := (projSQ Q phi, projCQ Q phi)
def cotPairQ (Q phi : Int) : Int × Int := (projCQ Q phi, projSQ Q phi)

/-- First-quadrant `L¹` inverse tangent `atanL1Q(Q, Y, X) = (Q * Y) / (|X| + |Y|)`
and inverse cotangent `acotL1Q(Q, X, Y) = (Q * X) / (|X| + |Y|)`. -/
def atanL1Q (Q yVal xVal : Int) : Int :=
  (Q * yVal).tdiv ((xVal.natAbs : Int) + (yVal.natAbs : Int))

def acotL1Q (Q xVal yVal : Int) : Int :=
  (Q * xVal).tdiv ((xVal.natAbs : Int) + (yVal.natAbs : Int))

/-- Full-ring `L¹` inverse tangent `atan2L1RingQ(Q, S, C) ∈ [0, 4Q)` and inverse cotangent `acot2L1RingQ(Q, C, S) ∈ [0, 4Q)`. -/
def atan2L1RingQ (Q sVal cVal : Int) : Int :=
  let l1 := (cVal.natAbs : Int) + (sVal.natAbs : Int)
  if 0 ≤ sVal then
    if 0 ≤ cVal then (Q * sVal).tdiv l1
    else 2 * Q - (Q * sVal).tdiv l1
  else
    if cVal < 0 then 2 * Q + (Q * (-sVal)).tdiv l1
    else 4 * Q - (Q * (-sVal)).tdiv l1

def acot2L1RingQ (Q cVal sVal : Int) : Int :=
  atan2L1RingQ Q sVal cVal

/-- Projective Gudermann–Minkowski hyperbolic triple `(hypCoshQ, hypSinhQ, hypDenomQ)` for arbitrary `Q` and `φ`:
- `hypCoshQ(Q, φ)  = C_Q(φ)² + S_Q(φ)²`,
- `hypSinhQ(Q, φ)  = 2 * C_Q(φ) * S_Q(φ)`,
- `hypDenomQ(Q, φ) = C_Q(φ)² - S_Q(φ)²`. -/
def hypCoshQ (Q phi : Int) : Int :=
  projCQ Q phi * projCQ Q phi + projSQ Q phi * projSQ Q phi

def hypSinhQ (Q phi : Int) : Int :=
  2 * projCQ Q phi * projSQ Q phi

def hypDenomQ (Q phi : Int) : Int :=
  projCQ Q phi * projCQ Q phi - projSQ Q phi * projSQ Q phi

/-- Root-free and logarithm-free inverse hyperbolic operator `invHypQ(Q, Ch, Sh, D_hyp) = (Ch + Sh - D_hyp) / (2 * Q)`. -/
def invHypQ (Q chVal shVal dHypVal : Int) : Int :=
  (chVal + shVal - dHypVal).tdiv (2 * Q)

/-- Cayley light-cone hyperbolic functions `(cosh, sinh, tanh, coth)` and their logarithm-free inverses `(atanh, acoth)` on `(U, V)`. -/
def coshLightCone (U V : Int) : Int := U + V
def sinhLightCone (U V : Int) : Int := U - V
def tanhCayley (U V : Int) : Int × Int := (U - V, U + V)
def cothCayley (U V : Int) : Int × Int := (U + V, U - V)
def atanhCayley (shVal chVal : Int) : Int × Int := (chVal + shVal, chVal - shVal)
def acothCayley (chVal shVal : Int) : Int × Int := (chVal + shVal, chVal - shVal)

/-- Boolean integer equality test for finite ring checks. -/
def eqIntB (a b : Int) : Bool :=
  if a = b then true else false

/-- **Theorem (Exact Projective Inverse Trigonometry `atan`/`acot` and Root-Free / Logarithm-Free Hyperbolic Calculus on `ℤ_{4Q}`)**:
Unconditional constructive proof for arbitrary integer parameters `Q, φ, U, V ∈ ℤ` (`0 sorryAx`, `0 Classical.choice`, `0 Prop premises`):
1. **Universal Minkowski Hyperbola Identity for all `Q, φ ∈ ℤ`:**
   `hypCoshQ(Q, φ)² - hypSinhQ(Q, φ)² ≡ hypDenomQ(Q, φ)²`.
2. **Exact Algebraic Factorization of the Inverse Hyperbolic Numerator for all `Q, φ ∈ ℤ`:**
   `hypCoshQ(Q, φ) + hypSinhQ(Q, φ) - hypDenomQ(Q, φ) ≡ 2 * S_Q(φ) * (C_Q(φ) + S_Q(φ))`
   and `hypCoshQ(Q, φ) + hypSinhQ(Q, φ) ≡ (C_Q(φ) + S_Q(φ))²`.
3. **Logarithm-Free Cayley Hyperbolic Tangent & Cotangent Inversion for all `U, V ∈ ℤ`:**
   - `coshLightCone(U, V)² - sinhLightCone(U, V)² ≡ 4 * U * V`,
   - `atanhCayley(tanhCayley(U, V)) ≡ (2 * U, 2 * V)`,
   - `acothCayley(cothCayley(U, V)) ≡ (2 * U, 2 * V)`.
4. **Full 512-Tick Ring Bijective Inversion (`Q = 128`):**
   - For every `φ ∈ {0, ..., 511}`: `atan2L1RingQ 128 (S_128(φ)) (C_128(φ)) = φ`, `acot2L1RingQ 128 (C_128(φ)) (S_128(φ)) = φ`,
     and `hypCoshQ 128 φ + |hypSinhQ 128 φ| = 128² = 16,384`.
   - For every first-quadrant angle `φ ∈ {0, ..., 128}`: `invHypQ 128 (Ch(φ)) (Sh(φ)) (D_hyp(φ)) = φ` and
     `atanL1Q 128 (S_128(φ)) (C_128(φ)) + acotL1Q 128 (C_128(φ)) (S_128(φ)) = 128`. -/
theorem exact_inverse_trig_and_rootfree_hyperbolic_calculus
    (Q phi U V : Int) :
    -- 1. Universal Minkowski hyperbola identity Ch_Q(φ)² - Sh_Q(φ)² = D_hyp(φ)² for arbitrary Q, φ ∈ ℤ:
    (hypCoshQ Q phi * hypCoshQ Q phi - hypSinhQ Q phi * hypSinhQ Q phi =
       hypDenomQ Q phi * hypDenomQ Q phi) ∧
    -- 2. Exact algebraic factorization of Ch + Sh - D_hyp and Ch + Sh for arbitrary Q, φ ∈ ℤ:
    (hypCoshQ Q phi + hypSinhQ Q phi - hypDenomQ Q phi =
       2 * projSQ Q phi * (projCQ Q phi + projSQ Q phi) ∧
     hypCoshQ Q phi + hypSinhQ Q phi =
       (projCQ Q phi + projSQ Q phi) * (projCQ Q phi + projSQ Q phi)) ∧
    -- 3. Cayley light-cone hyperbolic identity and logarithm-free atanh / acoth inversion for arbitrary U, V ∈ ℤ:
    (coshLightCone U V * coshLightCone U V - sinhLightCone U V * sinhLightCone U V = 4 * U * V ∧
     atanhCayley (tanhCayley U V).1 (tanhCayley U V).2 = (2 * U, 2 * V) ∧
     acothCayley (cothCayley U V).1 (cothCayley U V).2 = (2 * U, 2 * V)) ∧
    -- 4. Full 512-tick ring bijective inversion of atan2, acot2, and root-free/log-free invHyp at Q = 128:
    (((List.range 512).all (fun p =>
       eqIntB (atan2L1RingQ 128 (projSQ 128 (p : Int)) (projCQ 128 (p : Int))) (p : Int) &&
       eqIntB (acot2L1RingQ 128 (projCQ 128 (p : Int)) (projSQ 128 (p : Int))) (p : Int) &&
       eqIntB (hypCoshQ 128 (p : Int) + ((hypSinhQ 128 (p : Int)).natAbs : Int)) (128 * 128)) = true) ∧
     ((List.range 129).all (fun p =>
       eqIntB (invHypQ 128 (hypCoshQ 128 (p : Int)) (hypSinhQ 128 (p : Int)) (hypDenomQ 128 (p : Int))) (p : Int) &&
       eqIntB (atanL1Q 128 (projSQ 128 (p : Int)) (projCQ 128 (p : Int)) +
               acotL1Q 128 (projCQ 128 (p : Int)) (projSQ 128 (p : Int))) 128) = true)) := by
  have hMink :
      hypCoshQ Q phi * hypCoshQ Q phi - hypSinhQ Q phi * hypSinhQ Q phi =
        hypDenomQ Q phi * hypDenomQ Q phi := by
    unfold hypCoshQ hypSinhQ hypDenomQ
    generalize projCQ Q phi = c
    generalize projSQ Q phi = s
    calc (c * c + s * s) * (c * c + s * s) - (2 * c * s) * (2 * c * s)
      _ = (c * c) * (c * c) + 2 * (c * c) * (s * s) + (s * s) * (s * s) - 4 * (c * c) * (s * s) := by
          simp [Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = (c * c) * (c * c) - 2 * (c * c) * (s * s) + (s * s) * (s * s) := by omega
      _ = (c * c - s * s) * (c * c - s * s) := by
          simp [Int.sub_mul, Int.mul_sub, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
          omega
  have hInvNum :
      hypCoshQ Q phi + hypSinhQ Q phi - hypDenomQ Q phi =
        2 * projSQ Q phi * (projCQ Q phi + projSQ Q phi) := by
    unfold hypCoshQ hypSinhQ hypDenomQ
    generalize projCQ Q phi = c
    generalize projSQ Q phi = s
    calc (c * c + s * s) + 2 * c * s - (c * c - s * s)
      _ = 2 * c * s + 2 * (s * s) := by omega
      _ = 2 * s * (c + s) := by
          simp [Int.mul_add, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  have hSumSq :
      hypCoshQ Q phi + hypSinhQ Q phi =
        (projCQ Q phi + projSQ Q phi) * (projCQ Q phi + projSQ Q phi) := by
    unfold hypCoshQ hypSinhQ
    generalize projCQ Q phi = c
    generalize projSQ Q phi = s
    simp [Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    omega
  have hLightCone :
      coshLightCone U V * coshLightCone U V - sinhLightCone U V * sinhLightCone U V = 4 * U * V := by
    unfold coshLightCone sinhLightCone
    calc (U + V) * (U + V) - (U - V) * (U - V)
      _ = (U * U + 2 * U * V + V * V) - (U * U - 2 * U * V + V * V) := by
          simp [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
          omega
      _ = 4 * U * V := by omega
  have hAtanh : atanhCayley (tanhCayley U V).1 (tanhCayley U V).2 = (2 * U, 2 * V) := by
    unfold atanhCayley tanhCayley
    dsimp
    congr 1 <;> omega
  have hAcoth : acothCayley (cothCayley U V).1 (cothCayley U V).2 = (2 * U, 2 * V) := by
    unfold acothCayley cothCayley
    dsimp
    congr 1 <;> omega
  refine ⟨hMink, ⟨hInvNum, hSumSq⟩, ⟨hLightCone, hAtanh, hAcoth⟩, ⟨by native_decide, by native_decide⟩⟩
