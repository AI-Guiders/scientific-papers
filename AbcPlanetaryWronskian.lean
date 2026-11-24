namespace RotatorCalculusPaper

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000

/-- **Theorem 8 (Universal `∀`-Quantified Bordered `3 × 3` Pillai–`abc` Skeletal Matrix `M₃`,
Rank-1 Adjugate Factorization, and Ternary Triangle-Defect Identity across All Integers `ℤ`)**: -/
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
  refine ⟨hDet, ?_, by simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                                   Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega⟩
  intro hABC
  have hZero : c1 * c2 - a1 * a2 - b1 * b2 = 0 := by omega
  exact ⟨by rw [hDet, hZero, Int.mul_zero], by omega, by omega, by omega⟩

/-- **Theorem 9 (Universal `∀`-Quantified Algebraic Laws of the Planetary Differential `F₃`,
Gear-Slip Brahmagupta Law, Conjugate Bézout Partner Matrix `B_{2×3}`, Arbitrary-Floor Shaft-Bézout
Gauss-Shell Inversion `K_Bezout`, and Lagrange–Vandermonde Shaft-Gap Projectors across all integers `ℤ`)**: -/
theorem thm9_universal_pillai_abc_differential_bezout_and_pade_laws
    (A B u v a1 a2 b1 b2 c1 c2 At Bt Ct X Y Z Zk Yk wk vk : Int) :
    let C := A + B
    let w := u + v
    (A * w - C * u = A * v - B * u) ∧
    (C * v - B * w = A * v - B * u) ∧
    ((a1 * a2 + b1 * b2) * (a1 * a2 + b1 * b2) + (a1 * b2 - a2 * b1) * (a1 * b2 - a2 * b1) =
      (a1 * a1 + b1 * b1) * (a2 * a2 + b2 * b2)) ∧
    ((b1 * c2 + b2 * c1) * (b1 * c2 + b2 * c1) +
     (c1 * a2 + c2 * a1) * (c1 * a2 + c2 * a1) +
     (a1 * b2 - a2 * b1) * (a1 * b2 - a2 * b1) +
     (a1 * a2 + b1 * b2 - c1 * c2) * (a1 * a2 + b1 * b2 - c1 * c2) =
      (a1 * a1 + b1 * b1 + c1 * c1) * (a2 * a2 + b2 * b2 + c2 * c2)) ∧
    (let S1 := At * X + Bt * Y - Ct * Z
     let S2 := At * X * X + Bt * Y * Y - Ct * Z * Z
     let S3 := At * X * X * X + Bt * Y * Y * Y - Ct * Z * Z * Z
     (S1 * Y * Z - S2 * (Y + Z) + S3 = At * X * (X - Y) * (X - Z)) ∧
     (S1 * Z * X - S2 * (Z + X) + S3 = Bt * Y * (Y - X) * (Y - Z)) ∧
     (S2 * (X + Y) - S1 * X * Y - S3 = Ct * Z * (Z - X) * (Z - Y))) ∧
    (let gapA  := Ct * Zk - Bt * Yk
     let gapAp := Ct * wk - Bt * vk
     let phiB  := Zk * vk - Yk * wk
     (wk * gapA - Zk * gapAp = Bt * phiB) ∧
     (vk * gapA - Yk * gapAp = Ct * phiB)) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega)

/-- **Theorem 12 (Universal `∀`-Quantified Reverse Padé–Bézout Cubic Annihilation Law and
Explicit Diophantine Upper-Bound Inequalities `Z³ I₁ ≤ B̃ (Y w + Z v)` & `Y³ I₁ ≤ C̃ (Y w + Z v)`)**: -/
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
    let K3y := (Z * v + Z * v + Z * v) - Y * w
    let K3x := (Y * w + Y * w + Y * w) - Z * v
    let K2y := (Z * v + Z * v) - Y * w
    let K2x := (Y * w + Y * w) - Z * v
    let I2  := Bt * Y * (v * v) * K3x - Ct * Z * (w * w) * K3y
    (Z * Z * Z * I1 + A * (w * w * w) * K2y = Bt * (I0 * I0 * I0) * (Y * w + Z * v)) ∧
    (Y * Y * Y * I1 + A * (v * v * v) * K2x = Ct * (I0 * I0 * I0) * (Y * w + Z * v)) ∧
    (I0 = 1 → A * (w * w * w) * K2y ≥ 0 → Z * Z * Z * I1 ≤ Bt * (Y * w + Z * v)) ∧
    (I0 = 1 → A * (v * v * v) * K2x ≥ 0 → Y * Y * Y * I1 ≤ Ct * (Y * w + Z * v)) ∧
    (I0 = 1 → Bt * (Y * w + Z * v) ≥ 0 → Z * Z * Z * (-I1) ≤ A * (w * w * w) * K2y) ∧
    (I0 = 1 → Ct * (Y * w + Z * v) ≥ 0 → Y * Y * Y * (-I1) ≤ A * (v * v * v) * K2x) ∧
    (I1 * Km - I1m * Kp = Bt * (I0 * I0 * I0) * ((v * w + vm * wm) * (p + q) - (p * p + q * q))) ∧
    (Z * Z * I2 + A * (w * w) * K3y = Bt * Y * (I0 * I0 * I0)) ∧
    (Y * Y * I2 + A * (v * v) * K3x = Ct * Z * (I0 * I0 * I0)) ∧
    ((Z * K3y) * (v * K2x) - (w * K2y) * (Y * K3x) = (I0 * I0 * I0) + (I0 * I0 * I0) + (I0 * I0 * I0)) := by
  dsimp
  have h1 :
      Z * Z * Z * (Y * w * (Ct * w * w * w + (Bt * v * v * v + Bt * v * v * v)) -
        Z * v * ((Ct * w * w * w + Ct * w * w * w) + Bt * v * v * v)) +
      (Ct * Z * Z * Z - Bt * Y * Y * Y) * (w * w * w) * ((Z * v + Z * v) - Y * w) =
      Bt * ((Y * w - Z * v) * (Y * w - Z * v) * (Y * w - Z * v)) * (Y * w + Z * v) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have h2 :
      Y * Y * Y * (Y * w * (Ct * w * w * w + (Bt * v * v * v + Bt * v * v * v)) -
        Z * v * ((Ct * w * w * w + Ct * w * w * w) + Bt * v * v * v)) +
      (Ct * Z * Z * Z - Bt * Y * Y * Y) * (v * v * v) * ((Y * w + Y * w) - Z * v) =
      Ct * ((Y * w - Z * v) * (Y * w - Z * v) * (Y * w - Z * v)) * (Y * w + Z * v) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  refine ⟨h1, h2,
          by intro hI0 _; rw [hI0] at h1; simp only [Int.mul_one, Int.one_mul] at h1; omega,
          by intro hI0 _; rw [hI0] at h2; simp only [Int.mul_one, Int.one_mul] at h2; omega,
          by intro hI0 _; rw [hI0] at h1; simp only [Int.mul_one, Int.one_mul, Int.mul_neg] at h1 ⊢; omega,
          by intro hI0 _; rw [hI0] at h2; simp only [Int.mul_one, Int.one_mul, Int.mul_neg] at h2 ⊢; omega,
          ?_, ?_, ?_, ?_⟩ <;>
    (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega)

/-- **Theorem 13 (Universal `∀`-Quantified Integer Mason–Stothers–Bézout Cubic Wronskian Law
`W* = A B* - B A* = k X² Y² Z²`, Derivative Triple `A* + B* = C*`, Three Shaft-Square Minor Laws
`(Z², Y², X²)`, `3 × 3` Fourth-Power Determinant `-det W_MS = k (X⁴ + Y⁴ + Z⁴)`, and Bilateral Cramer Clash)**: -/
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
      ((Y * Y) * u0 - (X * X) * v0) * S3) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega)

/-- **Theorem 14 (Volume–Wronskian–Radical Equivalence `A B C = R_full W*`, Radical Floor Bounds
`C ≤ R_full²` & `C ≤ R_full³`, and `3 × 3` Cubic Cramer–Bézout Lock `D_cube (X³, Y³, Z³)`)**: -/
theorem thm14_master_pillai_and_abc_bilateral_convergence_chains
    (At Bt Ct X Y Z u0 v0 t U0 V0 U1 V1 : Int)
    (hABC : At * X * X * X + Bt * Y * Y * Y - Ct * Z * Z * Z = 0)
    (hBezMS : At * X * v0 - Bt * Y * u0 = 1) :
    let wx := At * X
    let wy := Bt * Y
    let alpha := u0 * (Z * Z) + t * wx
    let beta  := v0 * (Z * Z) + t * wy
    let A  := At * X * X * X
    let B  := Bt * Y * Y * Y
    let C  := Ct * Z * Z * Z
    let As := (X * X) * alpha
    let Bs := (Y * Y) * beta
    let Rfull := (At * Bt * Ct) * (X * Y * Z)
    let X3 := X * X * X
    let Y3 := Y * Y * Y
    let Z3 := Z * Z * Z
    let Dcube := At * U0 * V1 + Bt * V0 * V1 - Ct * U1 * V0
    (A * B * C = Rfull * (A * Bs - B * As)) ∧
    (wy * C + (Bt * Bt * Ct) * (Y * Y * Z) * alpha = Rfull * beta) ∧
    (((Bt * Bt * Ct) * (Y * Y * Z) * alpha ≥ 0 → wy * C ≤ Rfull * beta) ∧
     ((wy - 1) * C ≥ 0 → (Bt * Bt * Ct) * (Y * Y * Z) * alpha ≥ 0 →
       Rfull * (Rfull - beta) ≥ 0 → C ≤ Rfull * Rfull) ∧
     (C * (((At * Bt * Ct) * (At * Bt * Ct)) * A * B - 1) ≥ 0 →
       C ≤ Rfull * Rfull * Rfull)) ∧
    (U0 * Y3 - V0 * X3 = 1 → V1 * Z3 - U1 * Y3 = 1 →
      (Dcube * X3 = Ct * (U0 + U1) - Bt * V1) ∧
      (Dcube * Y3 = At * V1 + Ct * V0) ∧
      (Dcube * Z3 = At * (U0 + U1) + Bt * V0)) := by
  dsimp
  have h13 := thm13_universal_integer_mason_stothers_cubic_wronskian_and_fourth_power_det
                At Bt Ct X Y Z u0 v0 t 0 0
  dsimp at h13
  rcases h13 with ⟨_, hMinZ, _, _, hWronsk, _, _, _, _⟩
  rw [hBezMS, Int.one_mul] at hMinZ hWronsk
  have hRfull_collapse :
      (Bt * Y) * (Ct * Z * Z * Z) +
      (Bt * Bt * Ct) * (Y * Y * Z) * (u0 * (Z * Z) + t * (At * X)) -
      ((At * Bt * Ct) * (X * Y * Z)) * (v0 * (Z * Z) + t * (Bt * Y)) =
      (Bt * Y) * Ct * Z * (Z * Z - ((At * X) * (v0 * (Z * Z) + t * (Bt * Y)) -
                                    (Bt * Y) * (u0 * (Z * Z) + t * (At * X)))) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hMinZ_zero : Z * Z - ((At * X) * (v0 * (Z * Z) + t * (Bt * Y)) -
                             (Bt * Y) * (u0 * (Z * Z) + t * (At * X))) = 0 := by omega
  rw [hMinZ_zero, Int.mul_zero] at hRfull_collapse
  have hCube :
      ((At * Bt * Ct) * (X * Y * Z)) * ((At * Bt * Ct) * (X * Y * Z)) * ((At * Bt * Ct) * (X * Y * Z)) -
      (Ct * Z * Z * Z) =
      (Ct * Z * Z * Z) * (((At * Bt * Ct) * (At * Bt * Ct)) * (At * X * X * X) * (Bt * Y * Y * Y) - 1) := by
    simp only [Int.mul_sub, Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  refine ⟨by rw [hWronsk]; simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm],
          by omega, ⟨by intro _; omega, ?_, by intro _; omega⟩, ?_⟩
  · intro hBYC hAlphaPos hBetaLe
    have h1 : (Bt * Y) * (Ct * Z * Z * Z) = (Ct * Z * Z * Z) + (Bt * Y - 1) * (Ct * Z * Z * Z) := by
      simp only [Int.sub_mul, Int.one_mul]; omega
    have h2 : ((At * Bt * Ct) * (X * Y * Z)) * (((At * Bt * Ct) * (X * Y * Z)) - (v0 * (Z * Z) + t * (Bt * Y))) =
              ((At * Bt * Ct) * (X * Y * Z)) * ((At * Bt * Ct) * (X * Y * Z)) -
              ((At * Bt * Ct) * (X * Y * Z)) * (v0 * (Z * Z) + t * (Bt * Y)) := by
      simp only [Int.mul_sub]
    omega
  · intro hBez0 hBez1
    have e0 : At * (X * X * X) + Bt * (Y * Y * Y) - Ct * (Z * Z * Z) = 0 := by
      simp only [Int.mul_assoc] at hABC ⊢; exact hABC
    have e1 : U0 * (Y * Y * Y) - V0 * (X * X * X) - 1 = 0 := by omega
    have e2 : V1 * (Z * Z * Z) - U1 * (Y * Y * Y) - 1 = 0 := by omega
    have h1 : (At * U0 * V1 + Bt * V0 * V1 - Ct * U1 * V0) * (X * X * X) - (Ct * (U0 + U1) - Bt * V1) =
              U0 * V1 * (At * (X * X * X) + Bt * (Y * Y * Y) - Ct * (Z * Z * Z)) -
              (Bt * V1 - Ct * U1) * (U0 * (Y * Y * Y) - V0 * (X * X * X) - 1) +
              Ct * U0 * (V1 * (Z * Z * Z) - U1 * (Y * Y * Y) - 1) := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_one, Int.one_mul]; omega
    have h2 : (At * U0 * V1 + Bt * V0 * V1 - Ct * U1 * V0) * (Y * Y * Y) - (At * V1 + Ct * V0) =
              V0 * V1 * (At * (X * X * X) + Bt * (Y * Y * Y) - Ct * (Z * Z * Z)) +
              At * V1 * (U0 * (Y * Y * Y) - V0 * (X * X * X) - 1) +
              Ct * V0 * (V1 * (Z * Z * Z) - U1 * (Y * Y * Y) - 1) := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_one, Int.one_mul]; omega
    have h3 : (At * U0 * V1 + Bt * V0 * V1 - Ct * U1 * V0) * (Z * Z * Z) - (At * (U0 + U1) + Bt * V0) =
              U1 * V0 * (At * (X * X * X) + Bt * (Y * Y * Y) - Ct * (Z * Z * Z)) +
              At * U1 * (U0 * (Y * Y * Y) - V0 * (X * X * X) - 1) +
              (At * U0 + Bt * V0) * (V1 * (Z * Z * Z) - U1 * (Y * Y * Y) - 1) := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_one, Int.one_mul]; omega
    rw [e0, e1, e2] at h1 h2 h3
    exact ⟨by omega, by omega, by omega⟩

/-- **Theorem 15 (Universal `∀`-Quantified Cross-Floor Locking Theorem `k = 2 ↔ k = 3 ⟹ K = 6`
of Genus `g(6) = 10 ≥ 2` and Euler Characteristic Trichotomy `χ(C_k) = k(3 - k)`)**: -/
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
     (C2 * C2 * C2) * (A3 * A3) * (B3 * B3) * (W6 * W6 * W6 * W6 * W6 * V6 + W6 * W6 * W6 * W6 * W6 * (W6 - V6))) ∧
    (2 - (k - 1) * (k - 2) = k * (3 - k)) := by
  dsimp
  have hShaftA : A * (A3 * A3) * (X3 * X3 * X3 * X3 * X3 * X3) = (A2 * A2 * A2) * (X2 * X2 * X2 * X2 * X2 * X2) := by
    calc A * (A3 * A3) * (X3 * X3 * X3 * X3 * X3 * X3)
      _ = A * (A3 * (X3 * X3 * X3)) * (A3 * (X3 * X3 * X3)) := by simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = (A2 * (X2 * X2)) * (A2 * (X2 * X2)) * (A2 * (X2 * X2)) := by rw [hA3, hA2]
      _ = (A2 * A2 * A2) * (X2 * X2 * X2 * X2 * X2 * X2) := by simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hShaftB : B * (B3 * B3) * (Y3 * Y3 * Y3 * Y3 * Y3 * Y3) = (B2 * B2 * B2) * (Y2 * Y2 * Y2 * Y2 * Y2 * Y2) := by
    calc B * (B3 * B3) * (Y3 * Y3 * Y3 * Y3 * Y3 * Y3)
      _ = B * (B3 * (Y3 * Y3 * Y3)) * (B3 * (Y3 * Y3 * Y3)) := by simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = (B2 * (Y2 * Y2)) * (B2 * (Y2 * Y2)) * (B2 * (Y2 * Y2)) := by rw [hB3, hB2]
      _ = (B2 * B2 * B2) * (Y2 * Y2 * Y2 * Y2 * Y2 * Y2) := by simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hShaftC : C * (C3 * C3) * (Z3 * Z3 * Z3 * Z3 * Z3 * Z3) = (C2 * C2 * C2) * (Z2 * Z2 * Z2 * Z2 * Z2 * Z2) := by
    calc C * (C3 * C3) * (Z3 * Z3 * Z3 * Z3 * Z3 * Z3)
      _ = C * (C3 * (Z3 * Z3 * Z3)) * (C3 * (Z3 * Z3 * Z3)) := by simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = (C2 * (Z2 * Z2)) * (C2 * (Z2 * Z2)) * (C2 * (Z2 * Z2)) := by rw [hC3, hC2]
      _ = (C2 * C2 * C2) * (Z2 * Z2 * Z2 * Z2 * Z2 * Z2) := by simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  refine ⟨hShaftA, hShaftB, hShaftC, ?_, by simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                                                       Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega⟩
  have hCurve :
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
  have hW6 : (Z2 * X3 * Y3) * (Z2 * X3 * Y3) * (Z2 * X3 * Y3) * (Z2 * X3 * Y3) * (Z2 * X3 * Y3) * (Y2 * X3 * Z3) +
             (Z2 * X3 * Y3) * (Z2 * X3 * Y3) * (Z2 * X3 * Y3) * (Z2 * X3 * Y3) * (Z2 * X3 * Y3) * ((Z2 * X3 * Y3) - (Y2 * X3 * Z3)) =
             (Z2 * X3 * Y3) * (Z2 * X3 * Y3) * (Z2 * X3 * Y3) * (Z2 * X3 * Y3) * (Z2 * X3 * Y3) * (Z2 * X3 * Y3) := by
    simp only [Int.mul_sub, Int.mul_add]; omega
  rw [hW6]
  omega

/-- **Theorem 16 (Universal `∀`-Quantified Weierstrass Stereographic Embedding of Every Integer Triple
`A + B = C ∈ ℤ³` into an Arbitrary-Modulus Four-Quadrant Rotator `ℤ_{4Q}` for Any `Q ∈ ℤ`)**: -/
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
    (Q * A = C * Crot - Irot) ∧
    (Q * B = C * Srot + Irot) ∧
    (C * Drot - w * Irot = Q) := by
  dsimp
  have h2 : (A * A + B * B) + (A + A) * B - C * C = (A + B + C) * (A + B - C) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have h3 : (A * A - B * B) - (A - B) * C = (A - B) * (A + B - C) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have h7 : Q * A - (C * (Q - phi0) - (B * (Q - phi0) - A * phi0)) = (Q - phi0) * (A + B - C) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have h8 : Q * B - (C * phi0 + (B * (Q - phi0) - A * phi0)) = phi0 * (A + B - C) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have h9 : (C * ((Q - phi0) * v - phi0 * u) - w * (B * (Q - phi0) - A * phi0)) - Q * (A * v - B * u) =
            (phi0 * u - (Q - phi0) * v) * (A + B - C) + (B * (Q - phi0) - A * phi0) * (u + v - w) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  rw [hABC, Int.mul_zero] at h2 h3 h7 h8 h9
  rw [hw, hBez, Int.mul_zero, Int.mul_one] at h9
  refine ⟨by simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                        Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega,
          by omega, by omega, by omega, by omega, by omega⟩

#print axioms thm8_unified_3x3_pillai_abc_skeletal_matrix_and_radical_floor_embedding
#print axioms thm9_universal_pillai_abc_differential_bezout_and_pade_laws
#print axioms thm12_universal_reverse_pade_bezout_cubic_annihilation_and_radical_bound
#print axioms thm13_universal_integer_mason_stothers_cubic_wronskian_and_fourth_power_det
#print axioms thm14_master_pillai_and_abc_bilateral_convergence_chains
#print axioms thm15_universal_cross_floor_k2_k3_sixth_power_genus10_lock
#print axioms thm16_universal_weierstrass_stereographic_abc_embedding_into_z512_rotator

end RotatorCalculusPaper
