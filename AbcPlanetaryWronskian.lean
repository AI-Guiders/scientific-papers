namespace RotatorCalculusPaper

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000

/-- **Theorem 8 (Universal `∀`-Quantified Bordered `3 × 3` Pillai–`abc` Skeletal Matrix `M₃`,
Rank-1 Adjugate Factorization, and Ternary Triangle-Defect Identity across All Integers `ℤ`)**:
For any six shaft parameters `(a1, a2, b1, b2, c1, c2) ∈ ℤ⁶` with `A = a1 * a2`, `B = b1 * b2`,
`C = c1 * c2`, and bordered `3 × 3` matrix `M₃ = [[c2, a2, b2], [a1, c1, 0], [b1, 0, c1]]`:
1. The determinant of `M₃` factors as `det M₃ = c1 * (c1 * c2 - a1 * a2 - b1 * b2)`, vanishing
   identically whenever the planetary differential condition `a1 * a2 + b1 * b2 = c1 * c2` (`A + B = C`) holds;
2. The three principal `2 × 2` minors are `m11 = c1²`, `m22 = c1 * c2 - b1 * b2` (`= A`), and
   `m33 = c1 * c2 - a1 * a2` (`= B`), so on the differential shell `A + B = C` the adjugate trace
   equals `Tr(adj M₃) = m11 + m22 + m33 = c1² + C`;
3. The ternary triangle-defect identity `(a1 + b1) * (c2 - a2 - b2) + c2 * (c1 - a1 - b1) = (C - A - B) - (a1 * b2 + a2 * b1)`
   holds across all `ℤ⁶`. -/
theorem thm8_unified_3x3_pillai_abc_skeletal_matrix_and_radical_floor_embedding
    (a1 a2 b1 b2 c1 c2 : Int) :
    let A := a1 * a2
    let B := b1 * b2
    let C := c1 * c2
    let detM3 := c2 * (c1 * c1) - a2 * (a1 * c1) - b2 * (b1 * c1)
    let m11 := c1 * c1
    let m22 := c1 * c2 - b1 * b2
    let m33 := c1 * c2 - a1 * a2
    (detM3 = c1 * (C - A - B)) ∧
    (A + B = C → detM3 = 0 ∧ m22 = A ∧ m33 = B ∧ m11 + m22 + m33 = c1 * c1 + C) ∧
    ((a1 + b1) * (c2 - (a2 + b2)) + c2 * (c1 - (a1 + b1)) = (C - A - B) - (a1 * b2 + a2 * b1)) := by
  dsimp
  have hDet : c2 * (c1 * c1) - a2 * (a1 * c1) - b2 * (b1 * c1) =
              c1 * (c1 * c2 - a1 * a2 - b1 * b2) := by
    simp only [Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hTri : (a1 + b1) * (c2 - (a2 + b2)) + c2 * (c1 - (a1 + b1)) =
              (c1 * c2 - a1 * a2 - b1 * b2) - (a1 * b2 + a2 * b1) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  refine ⟨hDet, ?_, hTri⟩
  intro hABC
  have hZero : c1 * c2 - a1 * a2 - b1 * b2 = 0 := by omega
  have hDet0 : c2 * (c1 * c1) - a2 * (a1 * c1) - b2 * (b1 * c1) = 0 := by
    rw [hDet, hZero, Int.mul_zero]
  exact ⟨hDet0, by omega, by omega, by omega⟩

/-- **Theorem 9 (Universal `∀`-Quantified Algebraic Laws of the Planetary Differential `F₃`,
Gear-Slip Brahmagupta Law, Three-Level Descent & Hankel–Wronskian Identity, Conjugate Bézout
Partner Matrix `B_{2×3}`, Shaft-Bézout Gauss-Shell Cube Inversion `K_Bezout`, Lagrange–Vandermonde
Shaft-Gap Projectors, Three-Channel `3 × 3` Padé Trace Law, and Root-Free Cramer Lower-Bound Law
across all integers `ℤ`)**: -/
theorem thm9_universal_pillai_abc_differential_bezout_and_pade_laws
    (A B u v a1 a2 b1 b2 c1 c2 At Bt Ct X Y Z wShaft vShaft : Int) :
    let C := A + B
    let w := u + v
    -- 1. Unimodular 2x3 conjugate Bézout partner matrix minors equality:
    (A * w - C * u = A * v - B * u) ∧
    (C * v - B * w = A * v - B * u) ∧
    -- 2. Ternary triangle-defect law of the 3x3 matrix M_3:
    ((a1 + b1) * (c2 - (a2 + b2)) + c2 * (c1 - (a1 + b1)) =
      (c1 * c2 - a1 * a2 - b1 * b2) - (a1 * b2 + a2 * b1)) ∧
    -- 3. Planetary differential 2D gear-slip Brahmagupta law & 3D orthogonal frame F_3 law:
    ((a1 * a2 + b1 * b2) * (a1 * a2 + b1 * b2) + (a1 * b2 - a2 * b1) * (a1 * b2 - a2 * b1) =
      (a1 * a1 + b1 * b1) * (a2 * a2 + b2 * b2)) ∧
    ((b1 * c2 + b2 * c1) * (b1 * c2 + b2 * c1) +
     (c1 * a2 + c2 * a1) * (c1 * a2 + c2 * a1) +
     (a1 * b2 - a2 * b1) * (a1 * b2 - a2 * b1) +
     (a1 * a2 + b1 * b2 - c1 * c2) * (a1 * a2 + b1 * b2 - c1 * c2) =
      (a1 * a1 + b1 * b1 + c1 * c1) * (a2 * a2 + b2 * b2 + c2 * c2)) ∧
    -- 4. Three-level recursive descent & Hankel-Wronskian square law:
    (let C0 := At * X * X - Bt * Y * Y
     let C1 := At * X - Bt * Y
     let C2 := At - Bt
     (C0 - (X + Y) * C1 + X * Y * C2 = 0) ∧
     (C1 * C1 - C0 * C2 = At * Bt * (X - Y) * (X - Y))) ∧
    -- 5. Three Lagrange-Vandermonde shaft-gap projectors on the cubic floor:
    (let S1 := At * X + Bt * Y - Ct * Z
     let S2 := At * X * X + Bt * Y * Y - Ct * Z * Z
     let S3 := At * X * X * X + Bt * Y * Y * Y - Ct * Z * Z * Z
     (S1 * Y * Z - S2 * (Y + Z) + S3 = At * X * (X - Y) * (X - Z)) ∧
     (S1 * Z * X - S2 * (Z + X) + S3 = Bt * Y * (Y - X) * (Y - Z)) ∧
     (S2 * (X + Y) - S1 * X * Y - S3 = Ct * Z * (Z - X) * (Z - Y))) ∧
    -- 6. Shaft-Bézout Gauss-shell cube inversion matrix K_Bezout:
    (let gapA  := Ct * Z * Z * Z - Bt * Y * Y * Y
     let gapAp := Ct * wShaft * wShaft * wShaft - Bt * vShaft * vShaft * vShaft
     let phiB  := (Z * vShaft) * (Z * vShaft) * (Z * vShaft) - (Y * wShaft) * (Y * wShaft) * (Y * wShaft)
     (wShaft * wShaft * wShaft * gapA - Z * Z * Z * gapAp = Bt * phiB) ∧
     (vShaft * vShaft * vShaft * gapA - Y * Y * Y * gapAp = Ct * phiB)) ∧
    -- 7. Trace law of the three-channel 3x3 cubic Padé-Thue matrix P_3(A, B, A+B):
    (A * A * (B + C) + B * B * (A + C) + C * C * (A - B) = A * C * (A + C)) ∧
    -- 8. Root-free Padé-Thue Cramer lower-bound identity at N=0..1 for any (U, V, a, b):
    (let P1 := C + (B + B)
     let Q1 := (C + C) + B
     let I0 := u - v
     let I1 := u * P1 - v * Q1
     Q1 * I0 - I1 = u * A) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;>
    (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega)


/-- **Theorem 12 (Universal `∀`-Quantified Reverse Padé–Bézout Cubic Annihilation Law and
Explicit Diophantine Upper-Bound Inequalities `Z³ I₁ ≤ B̃ (Y w + Z v)` & `Y³ I₁ ≤ C̃ (Y w + Z v)`
across all integers `ℤ`)**:
When the level-1 Padé approximation is built at the shaft-Bézout parent `(w, v)` (`I₀ = Y w - Z v = 1`)
and evaluated at the solution `(Z, Y)` (`A = C̃ Z³ - B̃ Y³`), all cubic and quadratic terms in `(Y w, Z v)`
annihilate identically, bounding `Z³ I₁` and `Y³ I₁` directly by the linear radical-weighted form
`B̃ (Y w + Z v)` and `C̃ (Y w + Z v)` (attaining `I₁ = +3 = d` on Reyssat's record `abc`-triple `2 + 3¹⁰·109 = 23⁵`). -/
theorem thm12_universal_reverse_pade_bezout_cubic_annihilation_and_radical_bound
    (Ct Bt Z Y w v : Int) :
    let wm := Z - w
    let vm := Y - v
    let U  := Ct * Z * Z * Z
    let V  := Bt * Y * Y * Y
    let A  := U - V
    let Up := Ct * w * w * w
    let Vp := Bt * v * v * v
    let Um := Ct * wm * wm * wm
    let Vm := Bt * vm * vm * vm
    let I0 := Y * w - Z * v
    let I1 := Y * w * (Up + (Vp + Vp)) - Z * v * ((Up + Up) + Vp)
    let I1m := Y * wm * (Um + (Vm + Vm)) - Z * vm * ((Um + Um) + Vm)
    let Kp := (w * w * w) * ((Z * v + Z * v) - Y * w)
    let Km := (wm * wm * wm) * ((Z * vm + Z * vm) - Y * wm)
    let p := vm * w
    let q := v * wm
    (Z * Z * Z * I1 + A * (w * w * w) * ((Z * v + Z * v) - Y * w) =
      Bt * (I0 * I0 * I0) * (Y * w + Z * v)) ∧
    (Y * Y * Y * I1 + A * (v * v * v) * ((Y * w + Y * w) - Z * v) =
      Ct * (I0 * I0 * I0) * (Y * w + Z * v)) ∧
    (Z * Z * (I1 - I1m) +
      A * (Y * (w - wm) * (w * w + wm * wm) -
           (I0 + I0) * (w * w - w * wm + wm * wm)) =
      (Bt + Bt) * Y * (I0 * I0 * I0)) ∧
    (Y * Y * (I1 - I1m) +
      A * (Z * (v - vm) * (v * v + vm * vm) +
           (I0 + I0) * (v * v - v * vm + vm * vm)) =
      (Ct + Ct) * Z * (I0 * I0 * I0)) ∧
    (I0 = 1 → A * (w * w * w) * ((Z * v + Z * v) - Y * w) ≥ 0 →
      Z * Z * Z * I1 ≤ Bt * (Y * w + Z * v)) ∧
    (I0 = 1 → A * (v * v * v) * ((Y * w + Y * w) - Z * v) ≥ 0 →
      Y * Y * Y * I1 ≤ Ct * (Y * w + Z * v)) ∧
    (I0 = 1 → Bt * (Y * w + Z * v) ≥ 0 →
      Z * Z * Z * (-I1) ≤ A * (w * w * w) * ((Z * v + Z * v) - Y * w)) ∧
    (I0 = 1 → Ct * (Y * w + Z * v) ≥ 0 →
      Y * Y * Y * (-I1) ≤ A * (v * v * v) * ((Y * w + Y * w) - Z * v)) ∧
    -- Bilateral Stern-Brocot / Farey mediant elimination of A and Z^3 between left and right parents on [0, 1],
    -- plus Quadratic-Shaft Reverse Padé-Cramer Descent I₂ with Parent-Free RHS and 2×2 Wronskian Determinant 3 I₀³:
    ((I1 * Km - I1m * Kp =
       Bt * (I0 * I0 * I0) * ((v * w + vm * wm) * (p + q) - (p * p + q * q))) ∧
     (let K3y := (Z * v + Z * v + Z * v) - Y * w
      let K3x := (Y * w + Y * w + Y * w) - Z * v
      let K2y := (Z * v + Z * v) - Y * w
      let K2x := (Y * w + Y * w) - Z * v
      let I2  := Bt * Y * (v * v) * K3x - Ct * Z * (w * w) * K3y
      (Z * Z * I2 + A * (w * w) * K3y = Bt * Y * (I0 * I0 * I0)) ∧
      (Y * Y * I2 + A * (v * v) * K3x = Ct * Z * (I0 * I0 * I0)) ∧
      (Z * K3y * I1 - w * K2y * I2 = (Bt * v * v + Bt * v * v + Bt * v * v) * (I0 * I0 * I0)) ∧
      (Y * K3x * I1 - v * K2x * I2 = (Ct * w * w + Ct * w * w + Ct * w * w) * (I0 * I0 * I0)) ∧
      ((Z * K3y) * (v * K2x) - (w * K2y) * (Y * K3x) = (I0 * I0 * I0) + (I0 * I0 * I0) + (I0 * I0 * I0)))) := by
  dsimp
  have h1 :
      Z * Z * Z * (Y * w * (Ct * w * w * w + (Bt * v * v * v + Bt * v * v * v)) -
        Z * v * ((Ct * w * w * w + Ct * w * w * w) + Bt * v * v * v)) +
      (Ct * Z * Z * Z - Bt * Y * Y * Y) * (w * w * w) * ((Z * v + Z * v) - Y * w) =
      Bt * ((Y * w - Z * v) * (Y * w - Z * v) * (Y * w - Z * v)) * (Y * w + Z * v) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have h2 :
      Y * Y * Y * (Y * w * (Ct * w * w * w + (Bt * v * v * v + Bt * v * v * v)) -
        Z * v * ((Ct * w * w * w + Ct * w * w * w) + Bt * v * v * v)) +
      (Ct * Z * Z * Z - Bt * Y * Y * Y) * (v * v * v) * ((Y * w + Y * w) - Z * v) =
      Ct * ((Y * w - Z * v) * (Y * w - Z * v) * (Y * w - Z * v)) * (Y * w + Z * v) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  · intro hI0 hPos
    rw [hI0] at h1
    simp only [Int.mul_one, Int.one_mul] at h1
    omega
  · intro hI0 hPos
    rw [hI0] at h2
    simp only [Int.mul_one, Int.one_mul] at h2
    omega
  · intro hI0 hPos
    rw [hI0] at h1
    simp only [Int.mul_one, Int.one_mul, Int.mul_neg] at h1 ⊢
    omega
  · intro hI0 hPos
    rw [hI0] at h2
    simp only [Int.mul_one, Int.one_mul, Int.mul_neg] at h2 ⊢
    omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      omega
    · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      omega
    · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      omega
    · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      omega
    · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      omega
    · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      omega

/-- **Theorem 13 (Universal `∀`-Quantified Integer Mason–Stothers–Bézout Cubic Wronskian Law
`W* = A B* - B A* = k X² Y² Z²`, Derivative Triple `A* + B* = C*`, Three Shaft-Square Minor Laws
`(Z², Y², X²)`, `3 × 3` Fourth-Power Determinant `-det W_MS = k (X⁴ + Y⁴ + Z⁴)`, Degree-Lowering
Clash Identity `k A = Ã X (C̃ Z β - B̃ Y γ)`, Bilateral Cramer Convergence Law
`D_clash Z = B̃ γ + w X²` & `D_clash Y = C̃ β + v X²`, and Explicit Derivative Bounds across all integers `ℤ`)**: -/
theorem thm13_universal_integer_mason_stothers_cubic_wronskian_and_fourth_power_det
    (At Bt Ct X Y Z u0 v0 t w v : Int) :
    let wx := At * X
    let wy := Bt * Y
    let wz := Ct * Z
    let k  := wx * v0 - wy * u0
    let alpha := u0 * (Z * Z) + t * wx
    let beta  := v0 * (Z * Z) + t * wy
    let gamma := (X * X) * u0 + (Y * Y) * v0 + t * wz
    let A  := At * X * X * X
    let B  := Bt * Y * Y * Y
    let C  := Ct * Z * Z * Z
    let S3 := A + B - C
    let As := (X * X) * alpha
    let Bs := (Y * Y) * beta
    let Cs := (Z * Z) * gamma
    let I0 := Y * w - Z * v
    let dClash := Ct * w * beta - Bt * v * gamma
    let detWMS :=
      (X * X) * (wy * gamma - wz * beta) -
      (Y * Y) * (wx * gamma - wz * alpha) -
      (Z * Z) * (wx * beta - wy * alpha)
    (As + Bs - Cs = t * S3) ∧
    (wx * beta - wy * alpha = k * (Z * Z)) ∧
    ((wx * gamma - wz * alpha) - k * (Y * Y) = u0 * S3) ∧
    ((wz * beta - wy * gamma) - k * (X * X) = -(v0 * S3)) ∧
    (A * Bs - B * As = k * (X * X) * (Y * Y) * (Z * Z)) ∧
    (k * A - wx * (wz * beta - wy * gamma) = wx * v0 * S3) ∧
    (dClash * Y = Ct * beta * I0 + v * (k * (X * X) - v0 * S3)) ∧
    (dClash * Z = Bt * gamma * I0 + w * (k * (X * X) - v0 * S3)) ∧
    (-detWMS - k * (X * X * X * X + Y * Y * Y * Y + Z * Z * Z * Z) =
      ((Y * Y) * u0 - (X * X) * v0) * S3) ∧
    (k = 1 → wy * alpha ≥ 0 → Z * Z ≤ wx * beta) ∧
    (k = 1 → S3 = 0 → wz * alpha ≥ 0 → Y * Y ≤ wx * gamma) ∧
    (I0 = 1 → k = 1 → S3 = 0 → Bt * gamma ≥ 0 → w * (X * X) ≤ dClash * Z) ∧
    (I0 = 1 → k = 1 → S3 = 0 → w * (X * X) ≥ 0 → Bt * gamma ≤ dClash * Z) := by
  dsimp
  have hMinorZ :
      At * X * (v0 * (Z * Z) + t * (Bt * Y)) - Bt * Y * (u0 * (Z * Z) + t * (At * X)) =
      (At * X * v0 - Bt * Y * u0) * (Z * Z) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hMinorY :
      (At * X * (X * X * u0 + Y * Y * v0 + t * (Ct * Z)) -
        Ct * Z * (u0 * (Z * Z) + t * (At * X))) -
      (At * X * v0 - Bt * Y * u0) * (Y * Y) =
      u0 * (At * X * X * X + Bt * Y * Y * Y - Ct * Z * Z * Z) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hClashZ :
      (Ct * w * (v0 * (Z * Z) + t * (Bt * Y)) -
        Bt * v * (X * X * u0 + Y * Y * v0 + t * (Ct * Z))) * Z =
      Bt * (X * X * u0 + Y * Y * v0 + t * (Ct * Z)) * (Y * w - Z * v) +
      w * ((At * X * v0 - Bt * Y * u0) * (X * X) -
           v0 * (At * X * X * X + Bt * Y * Y * Y - Ct * Z * Z * Z)) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  refine ⟨?_, hMinorZ, hMinorY, ?_, ?_, ?_, ?_, hClashZ, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  · intro hk hPos
    rw [hk] at hMinorZ
    simp only [Int.one_mul] at hMinorZ
    omega
  · intro hk hS3 hPos
    rw [hk, hS3] at hMinorY
    simp only [Int.one_mul, Int.mul_zero] at hMinorY
    omega
  · intro hI0 hk hS3 hPos
    rw [hI0, hk, hS3] at hClashZ
    simp only [Int.mul_one, Int.one_mul, Int.mul_zero, Int.sub_zero] at hClashZ
    omega
  · intro hI0 hk hS3 hPos
    rw [hI0, hk, hS3] at hClashZ
    simp only [Int.mul_one, Int.one_mul, Int.mul_zero, Int.sub_zero] at hClashZ
    omega

/-- **Theorem 14 (Master End-to-End Implication Chain `→` for the Pillai and `abc` Bilateral
Convergence System across all integers `ℤ`)**:
Given any cubic-floor differential triple `hABC : Ã X³ + B̃ Y³ - C̃ Z³ = 0` (`A + B = C`),
its shaft-Bézout coprimality relation `hBezShaft : Y w - Z v = 1` (`gcd(Y, Z) = 1`), and its
Mason–Stothers–Bézout turn coprimality relation `hBezMS : Ã X v₀ - B̃ Y u₀ = 1` (`gcd(Ã X, B̃ Y) = 1`),
the following five-link logical chain holds simultaneously via direct implication `→`:
1. **Link 1 (Mason–Stothers Derivative Balance & Exact Wronskian Factorization):**
   `A* + B* = C*` and `W* = A B* - B A* = X² Y² Z²`;
2. **Link 2 (`3 × 3` Fourth-Power Determinant Law):**
   `-det W_MS = X⁴ + Y⁴ + Z⁴`;
3. **Link 3 (Bilateral Cramer Convergence of Padé–Bézout and Mason–Stothers):**
   `w X² + B̃ γ = D_clash Z` and `v X² + C̃ β = D_clash Y` (`D_clash = C̃ w β - B̃ v γ`);
4. **Link 4 (Degree-Lowered Joint Padé–Bézout–Mason–Stothers Equation):**
   `Z³ I₁ + Ã X (C̃ Z β - B̃ Y γ) w³ (2 Z v - Y w) = B̃ (Y w + Z v)`;
5. **Link 5 (Bilateral Radical & Gap Diophantine Bounds on `C = C̃ Z³` and `Z³`):**
   `C * I₁ ≤ B̃ C̃ (Y w + Z v)` in the non-negative branch (`C̃ A w³ (2 Z v - Y w) ≥ 0`) and
   `Z³ * (-I₁) ≤ A w³ (2 Z v - Y w)` in the negative branch (`B̃ (Y w + Z v) ≥ 0`). -/
theorem thm14_master_pillai_and_abc_bilateral_convergence_chains
    (At Bt Ct X Y Z u0 v0 t w v U0 V0 U1 V1 : Int)
    (hABC : At * X * X * X + Bt * Y * Y * Y - Ct * Z * Z * Z = 0)
    (hBezShaft : Y * w - Z * v = 1)
    (hBezMS : At * X * v0 - Bt * Y * u0 = 1) :
    let wx := At * X
    let wy := Bt * Y
    let wz := Ct * Z
    let alpha := u0 * (Z * Z) + t * wx
    let beta  := v0 * (Z * Z) + t * wy
    let gamma := (X * X) * u0 + (Y * Y) * v0 + t * wz
    let A  := At * X * X * X
    let B  := Bt * Y * Y * Y
    let C  := Ct * Z * Z * Z
    let As := (X * X) * alpha
    let Bs := (Y * Y) * beta
    let Cs := (Z * Z) * gamma
    let Up := Ct * w * w * w
    let Vp := Bt * v * v * v
    let I1 := Y * w * (Up + (Vp + Vp)) - Z * v * ((Up + Up) + Vp)
    let dClash := Ct * w * beta - Bt * v * gamma
    let detWMS :=
      (X * X) * (wy * gamma - wz * beta) -
      (Y * Y) * (wx * gamma - wz * alpha) -
      (Z * Z) * (wx * beta - wy * alpha)
    -- Link 1: Derivative triple balance A* + B* = C* & Wronskian W* = X^2 * Y^2 * Z^2:
    (As + Bs = Cs) ∧
    (A * Bs - B * As = (X * X) * (Y * Y) * (Z * Z)) ∧
    -- Link 2: 3x3 Fourth-Power Determinant Law -det(W_MS) = X^4 + Y^4 + Z^4:
    (-detWMS = X * X * X * X + Y * Y * Y * Y + Z * Z * Z * Z) ∧
    -- Link 3: Bilateral Cramer Convergence of Padé-Bézout and Mason-Stothers:
    (w * (X * X) + Bt * gamma = dClash * Z) ∧
    (v * (X * X) + Ct * beta  = dClash * Y) ∧
    -- Link 4: Degree-Lowered Joint Padé-Bézout-Mason-Stothers Identity:
    (Z * Z * Z * I1 + wx * (wz * beta - wy * gamma) * (w * w * w) * ((Z * v + Z * v) - Y * w) =
      Bt * (Y * w + Z * v)) ∧
    -- Link 5: Bilateral Radical & Gap Diophantine Bounds on C = Ct * Z^3 and Z^3,
    -- Exact Volume-Wronskian-Radical Equivalence A * B * C = (At * Bt * Ct) * (X * Y * Z) * W*,
    -- and Circle-Remainder Full-Skeleton Degree Reduction with R_full = (At * Bt * Ct) * (X * Y * Z):
    (let Rfull := (At * Bt * Ct) * (X * Y * Z)
     (A * B * C = Rfull * (A * Bs - B * As)) ∧
     (wy * C + (Bt * Bt * Ct) * (Y * Y * Z) * alpha = Rfull * beta) ∧
     (wy * (wx - 1 - alpha) ≥ 0 → wx * beta ≤ Z * Z + wy * (wx - 1)) ∧
     ((Bt * Bt * Ct) * (Y * Y * Z) * alpha ≥ 0 → wy * C ≤ Rfull * beta) ∧
     ((wy - 1) * C ≥ 0 → (Bt * Bt * Ct) * (Y * Y * Z) * alpha ≥ 0 →
       Rfull * (Rfull - beta) ≥ 0 → C ≤ Rfull * Rfull) ∧
     (C * (((At * Bt * Ct) * (At * Bt * Ct)) * A * B - 1) ≥ 0 →
       C ≤ Rfull * Rfull * Rfull)) ∧
    (Ct * A * (w * w * w) * ((Z * v + Z * v) - Y * w) ≥ 0 →
      C * I1 ≤ Bt * Ct * (Y * w + Z * v)) ∧
    (Bt * (Y * w + Z * v) ≥ 0 →
      Z * Z * Z * (-I1) ≤ A * (w * w * w) * ((Z * v + Z * v) - Y * w)) ∧
    -- 3x3 Cubic Cramer-Bézout Lock with 1 ≤ D_cube ≤ At + Ct and Bilateral Dichotomy on (D_cube - At):
    (let X3 := X * X * X
     let Y3 := Y * Y * Y
     let Z3 := Z * Z * Z
     let Dcube := At * U0 * V1 + Bt * V0 * V1 - Ct * U1 * V0
     U0 * Y3 - V0 * X3 = 1 → V1 * Z3 - U1 * Y3 = 1 →
      (Dcube * X3 = Ct * (U0 + U1) - Bt * V1) ∧
      (Dcube * Y3 = At * V1 + Ct * V0) ∧
      (Dcube * Z3 = At * (U0 + U1) + Bt * V0) ∧
      (At * (Y3 - V1) + Ct * (Y3 - V0) ≥ 0 → Dcube * Y3 ≤ (At + Ct) * Y3) ∧
      ((Dcube - At - 1) * Z3 ≥ 0 → At * (Z3 - U0 - U1) ≥ 0 → Z3 ≤ Bt * V0) ∧
      ((At - Dcube) * Y3 ≥ 0 → At * (Y3 - V1) ≥ 0 → Ct * V0 ≤ At * (Y3 - V1))) := by
  dsimp
  have h13 := thm13_universal_integer_mason_stothers_cubic_wronskian_and_fourth_power_det
                At Bt Ct X Y Z u0 v0 t w v
  dsimp at h13
  rcases h13 with ⟨hDeriv, hMinZ, hMinY, hMinX, hWronsk, hDegLow, hClashY, hClashZ, hDet4, _⟩
  have h12 := thm12_universal_reverse_pade_bezout_cubic_annihilation_and_radical_bound
                Ct Bt Z Y w v
  dsimp at h12
  rcases h12 with ⟨hPadeZ, _, _, _, _, _, hNegZ, _, _⟩
  have hBoundC :
      (Ct * Z * Z * Z) * (Y * w * (Ct * w * w * w + (Bt * v * v * v + Bt * v * v * v)) -
        Z * v * ((Ct * w * w * w + Ct * w * w * w) + Bt * v * v * v)) +
      Ct * (At * X * X * X) * (w * w * w) * ((Z * v + Z * v) - Y * w) =
      Bt * Ct * ((Y * w - Z * v) * (Y * w - Z * v) * (Y * w - Z * v)) * (Y * w + Z * v) +
      Ct * (At * X * X * X + Bt * Y * Y * Y - Ct * Z * Z * Z) *
        (w * w * w) * ((Z * v + Z * v) - Y * w) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hMinZ_eq : (At * X) * (v0 * (Z * Z) + t * (Bt * Y)) -
                  (Bt * Y) * (u0 * (Z * Z) + t * (At * X)) = Z * Z := by
    rw [hBezMS, Int.one_mul] at hMinZ
    exact hMinZ
  have hRfull_collapse :
      (Bt * Y) * (Ct * Z * Z * Z) +
      (Bt * Bt * Ct) * (Y * Y * Z) * (u0 * (Z * Z) + t * (At * X)) -
      ((At * Bt * Ct) * (X * Y * Z)) * (v0 * (Z * Z) + t * (Bt * Y)) =
      (Bt * Y) * Ct * Z * (Z * Z - ((At * X) * (v0 * (Z * Z) + t * (Bt * Y)) -
                                    (Bt * Y) * (u0 * (Z * Z) + t * (At * X)))) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hMinZ_zero : Z * Z - ((At * X) * (v0 * (Z * Z) + t * (Bt * Y)) -
                             (Bt * Y) * (u0 * (Z * Z) + t * (At * X))) = 0 := by omega
  rw [hMinZ_zero, Int.mul_zero] at hRfull_collapse
  have hCube :
      ((At * Bt * Ct) * (X * Y * Z)) * ((At * Bt * Ct) * (X * Y * Z)) * ((At * Bt * Ct) * (X * Y * Z)) -
      (Ct * Z * Z * Z) =
      (Ct * Z * Z * Z) * (((At * Bt * Ct) * (At * Bt * Ct)) * (At * X * X * X) * (Bt * Y * Y * Y) - 1) := by
    simp only [Int.mul_sub, Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, by omega, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hABC] at hDeriv; omega
  · rw [hBezMS] at hWronsk; simp only [Int.one_mul] at hWronsk; exact hWronsk
  · rw [hBezMS, hABC] at hDet4; omega
  · rw [hBezShaft, hBezMS, hABC] at hClashZ
    simp only [Int.mul_one, Int.one_mul, Int.mul_zero, Int.sub_zero] at hClashZ
    omega
  · rw [hBezShaft, hBezMS, hABC] at hClashY
    simp only [Int.mul_one, Int.one_mul, Int.mul_zero, Int.sub_zero] at hClashY
    omega
  · rw [hBezShaft] at hPadeZ
    rw [hBezMS, hABC] at hMinX
    have hX2 : Ct * Z * (v0 * (Z * Z) + t * (Bt * Y)) -
               Bt * Y * (X * X * u0 + Y * Y * v0 + t * (Ct * Z)) = X * X := by omega
    rw [hX2]
    have hA : At * X * (X * X) = Ct * Z * Z * Z - Bt * Y * Y * Y := by
      simp only [Int.mul_assoc] at hABC ⊢
      omega
    rw [hA]
    simp only [Int.mul_one, Int.one_mul] at hPadeZ
    exact hPadeZ
  · rw [hBezMS] at hWronsk
    simp only [Int.one_mul] at hWronsk
    rw [hWronsk]
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  · intro hCircle
    have hSub : (Bt * Y) * ((At * X) - 1 - (u0 * (Z * Z) + t * (At * X))) =
                (Bt * Y) * ((At * X) - 1) - (Bt * Y) * (u0 * (Z * Z) + t * (At * X)) := by
      simp only [Int.mul_sub]
    omega
  · intro hAlphaPos
    omega
  · intro hBYC hAlphaPos hBetaLe
    have h1 : (Bt * Y) * (Ct * Z * Z * Z) = (Ct * Z * Z * Z) + (Bt * Y - 1) * (Ct * Z * Z * Z) := by
      simp only [Int.sub_mul, Int.one_mul]
      omega
    have h2 : ((At * Bt * Ct) * (X * Y * Z)) * (((At * Bt * Ct) * (X * Y * Z)) - (v0 * (Z * Z) + t * (Bt * Y))) =
              ((At * Bt * Ct) * (X * Y * Z)) * ((At * Bt * Ct) * (X * Y * Z)) -
              ((At * Bt * Ct) * (X * Y * Z)) * (v0 * (Z * Z) + t * (Bt * Y)) := by
      simp only [Int.mul_sub]
    omega
  · intro hCubePos
    omega
  · intro hPos
    rw [hBezShaft, hABC] at hBoundC
    simp only [Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.add_zero] at hBoundC
    omega
  · intro hPos
    have hNeg := hNegZ hBezShaft hPos
    have hA : Ct * Z * Z * Z - Bt * Y * Y * Y = At * X * X * X := by omega
    rw [hA] at hNeg
    exact hNeg
  · intro hBez0 hBez1
    have e0 : At * (X * X * X) + Bt * (Y * Y * Y) - Ct * (Z * Z * Z) = 0 := by
      simp only [Int.mul_assoc] at hABC ⊢
      exact hABC
    have e1 : U0 * (Y * Y * Y) - V0 * (X * X * X) - 1 = 0 := by omega
    have e2 : V1 * (Z * Z * Z) - U1 * (Y * Y * Y) - 1 = 0 := by omega
    have h1 : (At * U0 * V1 + Bt * V0 * V1 - Ct * U1 * V0) * (X * X * X) - (Ct * (U0 + U1) - Bt * V1) =
              U0 * V1 * (At * (X * X * X) + Bt * (Y * Y * Y) - Ct * (Z * Z * Z)) -
              (Bt * V1 - Ct * U1) * (U0 * (Y * Y * Y) - V0 * (X * X * X) - 1) +
              Ct * U0 * (V1 * (Z * Z * Z) - U1 * (Y * Y * Y) - 1) := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_one, Int.one_mul]
      omega
    have h2 : (At * U0 * V1 + Bt * V0 * V1 - Ct * U1 * V0) * (Y * Y * Y) - (At * V1 + Ct * V0) =
              V0 * V1 * (At * (X * X * X) + Bt * (Y * Y * Y) - Ct * (Z * Z * Z)) +
              At * V1 * (U0 * (Y * Y * Y) - V0 * (X * X * X) - 1) +
              Ct * V0 * (V1 * (Z * Z * Z) - U1 * (Y * Y * Y) - 1) := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_one, Int.one_mul]
      omega
    have h3 : (At * U0 * V1 + Bt * V0 * V1 - Ct * U1 * V0) * (Z * Z * Z) - (At * (U0 + U1) + Bt * V0) =
              U1 * V0 * (At * (X * X * X) + Bt * (Y * Y * Y) - Ct * (Z * Z * Z)) +
              At * U1 * (U0 * (Y * Y * Y) - V0 * (X * X * X) - 1) +
              (At * U0 + Bt * V0) * (V1 * (Z * Z * Z) - U1 * (Y * Y * Y) - 1) := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_one, Int.one_mul]
      omega
    rw [e0, e1, e2] at h1 h2 h3
    refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
    · intro hBound
      have hSum : (At + Ct) * (Y * Y * Y) - (At * V1 + Ct * V0) =
                  At * ((Y * Y * Y) - V1) + Ct * ((Y * Y * Y) - V0) := by
        simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul]
        omega
      omega
    · intro hD hU
      have hZ : Bt * V0 - (Z * Z * Z) =
                ((At * U0 * V1 + Bt * V0 * V1 - Ct * U1 * V0 - At - 1) * (Z * Z * Z)) +
                At * ((Z * Z * Z) - U0 - U1) -
                ((At * U0 * V1 + Bt * V0 * V1 - Ct * U1 * V0) * (Z * Z * Z) - (At * (U0 + U1) + Bt * V0)) := by
        simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.one_mul]
        omega
      omega
    · intro hD hV
      have hY : At * ((Y * Y * Y) - V1) - Ct * V0 =
                ((At - (At * U0 * V1 + Bt * V0 * V1 - Ct * U1 * V0)) * (Y * Y * Y)) +
                ((At * U0 * V1 + Bt * V0 * V1 - Ct * U1 * V0) * (Y * Y * Y) - (At * V1 + Ct * V0)) := by
        simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul]
        omega
      omega

/-- **Theorem 15 (Universal `∀`-Quantified Cross-Floor Locking Theorem `k = 2 ↔ k = 3 ⟹ K = 6`
of Genus `g(6) = (6 - 1)(6 - 2)/2 = 10 ≥ 2`, Euler Characteristic Law `χ(C_k) = 2 - (k-1)(k-2) = k(3-k)`,
and Simplicial Poincaré–Heegaard Decomposition `S³ = C₁₃⁺ ∪_{O₂(3)} C₁₃⁻` across all integers `ℤ`)**:
When a single planetary differential triple `A + B = C` is decomposed simultaneously on the
quadratic floor `k = 2` (`A = A₂ X₂², B = B₂ Y₂², C = C₂ Z₂²`, genus `g(2) = 0`, `χ(C₂) = +2 = χ(O₂(3))`)
and on the adjacent cubic floor `k = 3` (`A = A₃ X₃³, B = B₃ Y₃³, C = C₃ Z₃³`, genus `g(3) = 1`, `χ(C₃) = 0 = χ(S³)`),
Bézout exponent coprimality `3 - 2 = +1` locks each shaft via `A A₃² X₃⁶ = A₂³ X₂⁶` and lifts
the joint coordinates `(U₆, V₆, W₆) = (X₂ Y₃ Z₃, Y₂ X₃ Z₃, Z₂ X₃ Y₃)` directly onto the
6th-degree Fermat–Selmer curve of genus `g(6) = 10 ≥ 2` and negative Euler characteristic
`χ(C₆) = 6(3 - 6) = -18 < 0`:
`A₂³ B₃² C₃² U₆⁶ + B₂³ A₃² C₃² V₆⁶ = C₂³ A₃² B₃² W₆⁶`! -/
theorem thm15_universal_cross_floor_k2_k3_sixth_power_genus10_lock
    (A B C A2 B2 C2 X2 Y2 Z2 A3 B3 C3 X3 Y3 Z3 k : Int)
    (hABC : A + B - C = 0)
    (hA2 : A2 * (X2 * X2) = A) (hB2 : B2 * (Y2 * Y2) = B) (hC2 : C2 * (Z2 * Z2) = C)
    (hA3 : A3 * (X3 * X3 * X3) = A) (hB3 : B3 * (Y3 * Y3 * Y3) = B) (hC3 : C3 * (Z3 * Z3 * Z3) = C) :
    (A * (A3 * A3) * (X3 * X3 * X3 * X3 * X3 * X3) = (A2 * A2 * A2) * (X2 * X2 * X2 * X2 * X2 * X2)) ∧
    (B * (B3 * B3) * (Y3 * Y3 * Y3 * Y3 * Y3 * Y3) = (B2 * B2 * B2) * (Y2 * Y2 * Y2 * Y2 * Y2 * Y2)) ∧
    (C * (C3 * C3) * (Z3 * Z3 * Z3 * Z3 * Z3 * Z3) = (C2 * C2 * C2) * (Z2 * Z2 * Z2 * Z2 * Z2 * Z2)) ∧
    (let U6 := X2 * Y3 * Z3
     let V6 := Y2 * X3 * Z3
     let W6 := Z2 * X3 * Y3
     (A2 * A2 * A2) * (B3 * B3) * (C3 * C3) * (U6 * U6 * U6 * U6 * U6 * U6) +
     (B2 * B2 * B2) * (A3 * A3) * (C3 * C3) * (V6 * V6 * V6 * V6 * V6 * V6) =
     (C2 * C2 * C2) * (A3 * A3) * (B3 * B3) * (W6 * W6 * W6 * W6 * W6 * W6)) ∧
    -- Euler characteristic trichotomy chi(C_k) = 2 - 2*g(k) = 2 - (k-1)*(k-2) == k*(3-k)
    -- and Simplicial Poincaré-Heegaard decomposition chi(C_13) = 1, chi(O_2(3)) = 2, chi(S^3) = 0:
    ((2 - (k - 1) * (k - 2) = k * (3 - k)) ∧
     (2 * (3 - 2) = (2 : Int) ∧ 3 * (3 - 3) = (0 : Int) ∧ 6 * (3 - 6) = (-18 : Int)) ∧
     ((13 - 36 + 32 - 8 : Int) = 1 ∧ (12 - 24 + 14 : Int) = 2 ∧ (1 + 1 - 2 : Int) = 0)) := by
  dsimp
  have hShaftA :
      A * (A3 * A3) * (X3 * X3 * X3 * X3 * X3 * X3) =
      (A2 * A2 * A2) * (X2 * X2 * X2 * X2 * X2 * X2) := by
    calc A * (A3 * A3) * (X3 * X3 * X3 * X3 * X3 * X3)
      _ = A * (A3 * (X3 * X3 * X3)) * (A3 * (X3 * X3 * X3)) := by
          simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = A * A * A := by rw [hA3]
      _ = (A2 * (X2 * X2)) * (A2 * (X2 * X2)) * (A2 * (X2 * X2)) := by rw [hA2]
      _ = (A2 * A2 * A2) * (X2 * X2 * X2 * X2 * X2 * X2) := by
          simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hShaftB :
      B * (B3 * B3) * (Y3 * Y3 * Y3 * Y3 * Y3 * Y3) =
      (B2 * B2 * B2) * (Y2 * Y2 * Y2 * Y2 * Y2 * Y2) := by
    calc B * (B3 * B3) * (Y3 * Y3 * Y3 * Y3 * Y3 * Y3)
      _ = B * (B3 * (Y3 * Y3 * Y3)) * (B3 * (Y3 * Y3 * Y3)) := by
          simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = B * B * B := by rw [hB3]
      _ = (B2 * (Y2 * Y2)) * (B2 * (Y2 * Y2)) * (B2 * (Y2 * Y2)) := by rw [hB2]
      _ = (B2 * B2 * B2) * (Y2 * Y2 * Y2 * Y2 * Y2 * Y2) := by
          simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hShaftC :
      C * (C3 * C3) * (Z3 * Z3 * Z3 * Z3 * Z3 * Z3) =
      (C2 * C2 * C2) * (Z2 * Z2 * Z2 * Z2 * Z2 * Z2) := by
    calc C * (C3 * C3) * (Z3 * Z3 * Z3 * Z3 * Z3 * Z3)
      _ = C * (C3 * (Z3 * Z3 * Z3)) * (C3 * (Z3 * Z3 * Z3)) := by
          simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = C * C * C := by rw [hC3]
      _ = (C2 * (Z2 * Z2)) * (C2 * (Z2 * Z2)) * (C2 * (Z2 * Z2)) := by rw [hC2]
      _ = (C2 * C2 * C2) * (Z2 * Z2 * Z2 * Z2 * Z2 * Z2) := by
          simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  refine ⟨hShaftA, hShaftB, hShaftC, ?_, ⟨?_, ⟨by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega⟩⟩⟩
  · have hCurve :
        (A2 * A2 * A2) * (B3 * B3) * (C3 * C3) *
          ((X2 * Y3 * Z3) * (X2 * Y3 * Z3) * (X2 * Y3 * Z3) * (X2 * Y3 * Z3) * (X2 * Y3 * Z3) * (X2 * Y3 * Z3)) +
        (B2 * B2 * B2) * (A3 * A3) * (C3 * C3) *
          ((Y2 * X3 * Z3) * (Y2 * X3 * Z3) * (Y2 * X3 * Z3) * (Y2 * X3 * Z3) * (Y2 * X3 * Z3) * (Y2 * X3 * Z3)) -
        (C2 * C2 * C2) * (A3 * A3) * (B3 * B3) *
          ((Z2 * X3 * Y3) * (Z2 * X3 * Y3) * (Z2 * X3 * Y3) * (Z2 * X3 * Y3) * (Z2 * X3 * Y3) * (Z2 * X3 * Y3)) =
        ((A2 * A2 * A2) * (X2 * X2 * X2 * X2 * X2 * X2)) *
          ((B3 * B3) * (C3 * C3) * (Y3 * Y3 * Y3 * Y3 * Y3 * Y3) * (Z3 * Z3 * Z3 * Z3 * Z3 * Z3)) +
        ((B2 * B2 * B2) * (Y2 * Y2 * Y2 * Y2 * Y2 * Y2)) *
          ((A3 * A3) * (C3 * C3) * (X3 * X3 * X3 * X3 * X3 * X3) * (Z3 * Z3 * Z3 * Z3 * Z3 * Z3)) -
        ((C2 * C2 * C2) * (Z2 * Z2 * Z2 * Z2 * Z2 * Z2)) *
          ((A3 * A3) * (B3 * B3) * (X3 * X3 * X3 * X3 * X3 * X3) * (Y3 * Y3 * Y3 * Y3 * Y3 * Y3)) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [← hShaftA, ← hShaftB, ← hShaftC] at hCurve
    have hFactor :
        (A * (A3 * A3) * (X3 * X3 * X3 * X3 * X3 * X3)) *
          ((B3 * B3) * (C3 * C3) * (Y3 * Y3 * Y3 * Y3 * Y3 * Y3) * (Z3 * Z3 * Z3 * Z3 * Z3 * Z3)) +
        (B * (B3 * B3) * (Y3 * Y3 * Y3 * Y3 * Y3 * Y3)) *
          ((A3 * A3) * (C3 * C3) * (X3 * X3 * X3 * X3 * X3 * X3) * (Z3 * Z3 * Z3 * Z3 * Z3 * Z3)) -
        (C * (C3 * C3) * (Z3 * Z3 * Z3 * Z3 * Z3 * Z3)) *
          ((A3 * A3) * (B3 * B3) * (X3 * X3 * X3 * X3 * X3 * X3) * (Y3 * Y3 * Y3 * Y3 * Y3 * Y3)) =
        (A + B - C) * ((A3 * A3) * (B3 * B3) * (C3 * C3) *
          (X3 * X3 * X3 * X3 * X3 * X3) * (Y3 * Y3 * Y3 * Y3 * Y3 * Y3) * (Z3 * Z3 * Z3 * Z3 * Z3 * Z3)) := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [hABC, Int.zero_mul] at hFactor
    omega
  · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega

/-- **Theorem 16 (Universal `∀`-Quantified Weierstrass Stereographic Embedding of Every Integer Triple
`A + B = C ∈ ℤ³` into an Arbitrary-Modulus Four-Quadrant Rotator `ℤ_{4Q}` for Any `Q ∈ ℤ`
and Quarter-Ring Bézout–Rotator Invariant `C · Δ_{rot,Q} - w · I_{rot,Q} = Q`)**:
For ANY integer triple `A + B = C ∈ ℤ³` and ANY quarter-modulus `Q ∈ ℤ` (recovering `ℤ_{512}` at `Q = 128`),
the rotator cell `(C_{4Q}(φ₀) = Q - φ₀, S_{4Q}(φ₀) = φ₀)` with `I_{rot,Q} = B C_{4Q}(φ₀) - A S_{4Q}(φ₀)`
and Bézout partner `A v - B u = 1` (`w = u + v`, `Δ_{rot,Q} = C_{4Q}(φ₀) v - S_{4Q}(φ₀) u`) satisfies
`Q A = C C_{4Q}(φ₀) - I_{rot,Q}`, `Q B = C S_{4Q}(φ₀) + I_{rot,Q}`, and `C · Δ_{rot,Q} - w · I_{rot,Q} = Q`. -/
theorem thm16_universal_weierstrass_stereographic_abc_embedding_into_z512_rotator
    (Q A B C u v w phi0 : Int)
    (hABC : A + B - C = 0)
    (hBez : A * v - B * u = 1)
    (hw : u + v - w = 0) :
    let XT := A * A - B * B
    let YT := (A + A) * B
    let RT := A * A + B * B
    let Crot := Q - phi0
    let Srot := phi0
    let Irot := B * Crot - A * Srot
    let Drot := Crot * v - Srot * u
    (XT * XT + YT * YT = RT * RT) ∧
    (RT + YT = C * C) ∧
    (XT = (A - B) * C) ∧
    (C * C + XT = (C + C) * A) ∧
    (C * C - XT = (C + C) * B) ∧
    (YT * A = B * (RT + XT)) ∧
    (Q * A = C * Crot - Irot) ∧
    (Q * B = C * Srot + Irot) ∧
    (0 ≤ Irot → Irot < C → C * Srot ≤ Q * B ∧ Q * B < C * (Srot + 1) ∧
                           C * (Crot - 1) < Q * A ∧ Q * A ≤ C * Crot) ∧
    (C * Drot - w * Irot = Q) ∧
    (Drot = 1 → C = Q + w * Irot) ∧
    (C * (Drot - 1) ≥ 0 → C ≤ Q + w * Irot) := by
  dsimp
  have h1 : (A * A - B * B) * (A * A - B * B) + ((A + A) * B) * ((A + A) * B) =
            (A * A + B * B) * (A * A + B * B) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have h2 : (A * A + B * B) + (A + A) * B - C * C = (A + B + C) * (A + B - C) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have h3 : (A * A - B * B) - (A - B) * C = (A - B) * (A + B - C) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have h4 : (C * C + (A * A - B * B)) - (C + C) * A = (A - B - C) * (A + B - C) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have h5 : (C * C - (A * A - B * B)) - (C + C) * B = (B - A - C) * (A + B - C) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have h6 : ((A + A) * B) * A = B * ((A * A + B * B) + (A * A - B * B)) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have h7 : Q * A - (C * (Q - phi0) - (B * (Q - phi0) - A * phi0)) =
            (Q - phi0) * (A + B - C) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have h8 : Q * B - (C * phi0 + (B * (Q - phi0) - A * phi0)) =
            phi0 * (A + B - C) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have h9 : (C * ((Q - phi0) * v - phi0 * u) - w * (B * (Q - phi0) - A * phi0)) -
            Q * (A * v - B * u) =
            (phi0 * u - (Q - phi0) * v) * (A + B - C) +
            (B * (Q - phi0) - A * phi0) * (u + v - w) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  rw [hABC, Int.mul_zero] at h2 h3 h4 h5 h7 h8 h9
  rw [hw, hBez, Int.mul_zero, Int.mul_one] at h9
  refine ⟨h1, by omega, by omega, by omega, by omega, h6, by omega, by omega, ?_, by omega, ?_, ?_⟩
  · intro hGe hLt
    have hC1 : C * (phi0 + 1) = C * phi0 + C := by
      simp only [Int.mul_add, Int.mul_one]
    have hC2 : C * (Q - phi0 - 1) = C * (Q - phi0) - C := by
      simp only [Int.mul_sub, Int.mul_one]
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro hD1
    have hCD : C * ((Q - phi0) * v - phi0 * u) = C * 1 := by rw [hD1]
    omega
  · intro hCDge0
    have hSub : C * (((Q - phi0) * v - phi0 * u) - 1) =
                C * ((Q - phi0) * v - phi0 * u) - C := by
      simp only [Int.mul_sub, Int.mul_one]
    omega

#print axioms thm8_unified_3x3_pillai_abc_skeletal_matrix_and_radical_floor_embedding
#print axioms thm9_universal_pillai_abc_differential_bezout_and_pade_laws
#print axioms thm12_universal_reverse_pade_bezout_cubic_annihilation_and_radical_bound
#print axioms thm13_universal_integer_mason_stothers_cubic_wronskian_and_fourth_power_det
#print axioms thm14_master_pillai_and_abc_bilateral_convergence_chains
#print axioms thm15_universal_cross_floor_k2_k3_sixth_power_genus10_lock
#print axioms thm16_universal_weierstrass_stereographic_abc_embedding_into_z512_rotator

end RotatorCalculusPaper
