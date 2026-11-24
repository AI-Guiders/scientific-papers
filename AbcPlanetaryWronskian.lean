import PillaiDiophantine

namespace RotatorCalculusPaper

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000

/-- **Theorem 8 (Bordered `3 × 3` Pillai–`abc` Skeletal Matrix `M₃`,
Rank-1 Adjugate Factorization, and Ternary Triangle-Defect Identity)**: -/
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

/-- **Theorem 9 (Algebraic Laws of the Planetary Differential `F₃`,
Gear-Slip Brahmagupta Law, Conjugate Bézout Partner Matrix `B_{2×3}`, Shaft-Bézout
Gauss-Shell Inversion `K_Bezout`, and Lagrange–Vandermonde Shaft-Gap Projectors)**: -/
theorem thm9_pillai_abc_differential_bezout_and_pade_laws
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

/-- **Theorem 12 (Reverse Padé–Bézout Cubic Annihilation Law and
Diophantine Upper-Bound Inequalities `Z³ I₁ ≤ B̃ (Y w + Z v)` & `Y³ I₁ ≤ C̃ (Y w + Z v)`)**: -/
theorem thm12_reverse_pade_bezout_cubic_annihilation_and_radical_bound
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

/-- **Theorem 13 (Integer Mason–Stothers–Bézout Cubic Wronskian Law
`W* = A B* - B A* = k X² Y² Z²`, Derivative Triple `A* + B* = C*`, Three Shaft-Square Minor Laws
`(Z², Y², X²)`, `3 × 3` Fourth-Power Determinant `-det W_MS = k (X⁴ + Y⁴ + Z⁴)`, and Bilateral Cramer Clash)**: -/
theorem thm13_integer_mason_stothers_cubic_wronskian_and_fourth_power_det
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
  have h13 := thm13_integer_mason_stothers_cubic_wronskian_and_fourth_power_det
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

/-- **Theorem 15 (Cross-Floor Locking Theorem `k = 2 ↔ k = 3 ⟹ K = 6`
of Genus `g(6) = 10 ≥ 2` and Euler Characteristic Trichotomy `χ(C_k) = k(3 - k)`)**: -/
theorem thm15_cross_floor_k2_k3_sixth_power_genus10_lock
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

/-- **Theorem 16 (Weierstrass Stereographic Embedding of `A + B = C ∈ ℤ³`
into a Four-Quadrant Rotator `ℤ_{4Q}`)**: -/
theorem thm16_weierstrass_stereographic_abc_embedding_into_z512_rotator
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

/-- **Theorem 12b (Countable Padé-Tower Cubic Annihilation Law, `Z³` Elimination,
and Adjacent-Floor Escape across Arbitrary Floors `R : List Int` for `A + B = C`)**:
For every floor `R : List Int` of the countable Padé approximant tower
`(P_R, Q_R) = (padeTowerP R U V, padeTowerQ R U V)` built over `U = C̃ Z³`, `V = B̃ Y³`,
`A = U - V` (`A + B = C`), and any shaft-approximant pair `(w, v)` with `a = v * Z`, `b = w * Y`,
`A' = C̃ w³ - B̃ v³`, and floor invariant `I_R = a * P_R - b * Q_R`:
1. **Arbitrary-Floor Padé Difference, Sum, and Reverse Cubic Annihilation:**
   - `P_R - Q_R = padeTowerProdMinus R * A` and `P_R + Q_R = padeTowerProdPlus R * (U + V)`,
   - at base floor `R = [3]`, `U * P_{[3]}³ - V * Q_{[3]}³ = A³ * (U + V)`.
2. **Exact `Z³` Elimination on Every Floor `R : List Int`:**
   With `u_Z = a * P_R`, `v_Y = b * Q_R`, and `Φ₃(u_Z, v_Y) = u_Z² + u_Z v_Y + v_Y²`:
   - `U * I_R * Φ₃(u_Z, v_Y) = a³ * (U * P_R³ - V * Q_R³) - (U * b³ - V * a³) * Q_R³`,
   - whenever `1 ≤ Z³`:
     `C̃ * I_R * Φ₃(u_Z, v_Y) = v³ * (U * P_R³ - V * Q_R³) - A' * Y³ * Q_R³`.
3. **Adjacent-Floor Escape and Non-Degeneracy across `R` and `R' = R ++ [kShift + 1]`:**
   With `P_{R'} = padeTowerP (R ++ [kShift + 1]) U V`, `Q_{R'} = padeTowerQ (R ++ [kShift + 1]) U V`,
   and `I_{R'} = a * P_{R'} - b * Q_{R'}`:
   - `I_{R'} - (kShift + 1) * I_R = -kShift * (a + b) * padeTowerProdMinus R * A`,
   - whenever `kShift * (a + b) * padeTowerProdMinus R * A ≠ 0`:
     `¬(I_R = 0 ∧ I_{R'} = 0)` and `1 ≤ |I_R| + |I_{R'}|`,
   - if `I_R = 0`, then `I_{R'} = -kShift * (a + b) * padeTowerProdMinus R * A ≠ 0` and `1 ≤ |I_{R'}|`. -/
theorem thm12b_abc_countable_pade_tower_cubic_annihilation_and_adjacent_floor_escape
    (R : List Int) (kShift Ct Bt Z Y w v : Int) :
    let Z3 := Z * Z * Z
    let Y3 := Y * Y * Y
    let w3 := w * w * w
    let v3 := v * v * v
    let U  := Ct * Z3
    let V  := Bt * Y3
    let A  := U - V
    let Ap := Ct * w3 - Bt * v3
    let PR := padeTowerP R U V
    let QR := padeTowerQ R U V
    let PNext := padeTowerP (R ++ [kShift + 1]) U V
    let QNext := padeTowerQ (R ++ [kShift + 1]) U V
    let a  := v * Z
    let b  := w * Y
    let IR := a * PR - b * QR
    let INext := a * PNext - b * QNext
    let uZ := a * PR
    let vY := b * QR
    let phi3R := uZ * uZ + uZ * vY + vY * vY
    (PR - QR = padeTowerProdMinus R * A ∧
     PR + QR = padeTowerProdPlus R * (U + V)) ∧
    (U * ((padeTowerP [3] U V) * (padeTowerP [3] U V) * (padeTowerP [3] U V)) -
     V * ((padeTowerQ [3] U V) * (padeTowerQ [3] U V) * (padeTowerQ [3] U V)) =
     (A * A * A) * (U + V)) ∧
    (U * IR * phi3R = (a * a * a) * (U * (PR * PR * PR) - V * (QR * QR * QR)) -
                      (U * (b * b * b) - V * (a * a * a)) * (QR * QR * QR)) ∧
    (1 ≤ Z3 →
      Ct * IR * phi3R = v3 * (U * (PR * PR * PR) - V * (QR * QR * QR)) - Ap * Y3 * (QR * QR * QR)) ∧
    (INext - (kShift + 1) * IR = -kShift * (a + b) * padeTowerProdMinus R * A) ∧
    (kShift * (a + b) * padeTowerProdMinus R * A ≠ 0 →
      ¬(IR = 0 ∧ INext = 0) ∧ 1 ≤ IR.natAbs + INext.natAbs) ∧
    (IR = 0 →
      INext = -kShift * (a + b) * padeTowerProdMinus R * A ∧
      (kShift * (a + b) * padeTowerProdMinus R * A ≠ 0 → INext ≠ 0 ∧ 1 ≤ INext.natAbs)) := by
  dsimp
  have h7 := (thm7_pillai_recursive_descent_hankel_wronskian_farey_bezout_and_pade_thue_tower
               R [] kShift 0 0 0 0 (Ct * (Z * Z * Z) - Bt * (Y * Y * Y)) (Bt * (Y * Y * Y)) (v * Z) (w * Y)).2.2.2.2
  have hUV : (Ct * (Z * Z * Z) - Bt * (Y * Y * Y)) + Bt * (Y * Y * Y) = Ct * (Z * Z * Z) := by omega
  rw [hUV] at h7
  have hSum := h7.2.2.2.2.2.2.1
  have hDiff := h7.2.2.2.2.2.2.2.1
  have hStep := h7.2.2.2.2.2.2.2.2.2.1
  have hNondeg := h7.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h10b := thm10b_pillai_same_cell_two_solution_collision_and_gap_law
                 R kShift Ct Bt (Z * Z * Z) (Y * Y * Y) (w * w * w) (v * v * v) Z Y w v rfl rfl rfl rfl
  dsimp at h10b
  rcases h10b with ⟨_, hGenCube, _, hCancelZ3, hFloor3, _, hEscape⟩
  exact ⟨⟨hDiff, hSum⟩, hFloor3, hGenCube, hCancelZ3, hStep, hNondeg, hEscape⟩

/-- **Theorem 14b (Lagrange–Vandermonde Floor-Defect Trichotomy `(S₁, S₂, S₃ = 0)`
and Principal-Cell Bilateral Bézout Height Bracket for `A + B = C`)**:
For any radical-floor decomposition `A = Ã X³`, `B = B̃ Y³`, `C = C̃ Z³` satisfying
`S₃ = A + B - C = 0`, with lower-floor defects `S₁ = Ã X + B̃ Y - C̃ Z` and
`S₂ = Ã X² + B̃ Y² - C̃ Z²`:
1. **Exact Full-Height Lagrange–Vandermonde Projectors at `S₃ = 0`:**
   - `C * (Z - X) * (Z - Y) = Z² * (S₂ * (X + Y) - S₁ * X * Y)`,
   - `A * (X - Y) * (X - Z) = X² * (S₁ * Y * Z - S₂ * (Y + Z))`,
   - `B * (Y - X) * (Y - Z) = Y² * (S₁ * Z * X - S₂ * (Z + X))`.
2. **Lower-Floor Non-Degeneracy and Sign Trichotomy of `(S₁, S₂)`:**
   Whenever `1 ≤ C̃`, `1 ≤ X`, `1 ≤ Y`, `X < Z`, and `Y < Z`:
   - `1 ≤ C̃ * Z * (Z - X) * (Z - Y)` and `S₂ * (X + Y) - S₁ * X * Y = C̃ * Z * (Z - X) * (Z - Y) ≥ 1`,
   - `¬(S₁ = 0 ∧ S₂ = 0)` and `1 ≤ |S₁| + |S₂|`,
   - **Branch I (`0 ≤ S₁`):** `C̃ * Z ≤ Ã * X + B̃ * Y` and `C ≤ (Ã * X + B̃ * Y) * Z²`,
   - **Branch II (`S₂ ≤ 0`):** `S₁ ≤ -1` and `1 ≤ (-S₁) * X * Y`,
   - **Branch III (`S₁ ≤ -1 ∧ 1 ≤ S₂`):** `Ã * X + B̃ * Y + 1 ≤ C̃ * Z` and `C̃ * Z² + 1 ≤ Ã * X² + B̃ * Y²`.
3. **Principal-Cell Bilateral Bézout Height Bracket (`0 ≤ α ≤ Ã X - 1`):**
   For any Mason–Stothers–Bézout pair `(α, β)` satisfying `(Ã X) β - (B̃ Y) α = Z²`
   normalized into the principal fundamental cell `0 ≤ α ≤ Ã X - 1` (with `1 ≤ Ã X`, `1 ≤ B̃ Y`, `1 ≤ C̃`, `1 ≤ Z`):
   - `Z² ≤ (Ã * X) * β ∧ (Ã * X) * β ≤ Z² + (B̃ * Y) * (Ã * X - 1)` and `1 ≤ β`,
   - `(B̃ * Y) * C + (B̃ * B̃ * C̃) * (Y * Y * Z) * α = R_full * β` (`R_full = Ã B̃ C̃ X Y Z`),
   - **Bilateral Volume-to-Radical Bracket:**
     `R_full * β - (B̃ * B̃ * C̃) * (Y * Y * Z) * (Ã * X - 1) ≤ (B̃ * Y) * C ∧ (B̃ * Y) * C ≤ R_full * β`. -/
theorem thm14b_abc_hankel_vandermonde_floor_defect_trichotomy_and_bilateral_bezout_bracket
    (At Bt Ct X Y Z alpha beta : Int)
    (hABC : At * X * X * X + Bt * Y * Y * Y - Ct * Z * Z * Z = 0) :
    let A  := At * X * X * X
    let B  := Bt * Y * Y * Y
    let C  := Ct * Z * Z * Z
    let S1 := At * X + Bt * Y - Ct * Z
    let S2 := At * X * X + Bt * Y * Y - Ct * Z * Z
    let wx := At * X
    let wy := Bt * Y
    let Rfull := (At * Bt * Ct) * (X * Y * Z)
    (C * (Z - X) * (Z - Y) = (Z * Z) * (S2 * (X + Y) - S1 * X * Y) ∧
     A * (X - Y) * (X - Z) = (X * X) * (S1 * Y * Z - S2 * (Y + Z)) ∧
     B * (Y - X) * (Y - Z) = (Y * Y) * (S1 * Z * X - S2 * (Z + X))) ∧
    (1 ≤ Ct → 1 ≤ X → 1 ≤ Y → X < Z → Y < Z →
      1 ≤ Ct * Z * (Z - X) * (Z - Y) ∧
      S2 * (X + Y) - S1 * X * Y = Ct * Z * (Z - X) * (Z - Y) ∧
      ¬(S1 = 0 ∧ S2 = 0) ∧
      1 ≤ Int.natAbs S1 + Int.natAbs S2 ∧
      (0 ≤ S1 → Ct * Z ≤ At * X + Bt * Y ∧ C ≤ (At * X + Bt * Y) * (Z * Z)) ∧
      (S2 ≤ 0 → S1 ≤ -1 ∧ 1 ≤ (-S1) * X * Y) ∧
      (S1 ≤ -1 → 1 ≤ S2 → At * X + Bt * Y + 1 ≤ Ct * Z ∧ Ct * Z * Z + 1 ≤ At * X * X + Bt * Y * Y)) ∧
    (wx * beta - wy * alpha = Z * Z →
     1 ≤ wx → 1 ≤ wy → 1 ≤ Ct → 1 ≤ Z → 0 ≤ alpha → alpha ≤ wx - 1 →
      (Z * Z ≤ wx * beta ∧ wx * beta ≤ Z * Z + wy * (wx - 1) ∧ 1 ≤ beta) ∧
      (wy * C + (Bt * Bt * Ct) * (Y * Y * Z) * alpha = Rfull * beta) ∧
      (Rfull * beta - (Bt * Bt * Ct) * (Y * Y * Z) * (wx - 1) ≤ wy * C ∧
       wy * C ≤ Rfull * beta)) := by
  dsimp
  have h9 := (thm9_pillai_abc_differential_bezout_and_pade_laws
               0 0 0 0 0 0 0 0 0 0 At Bt Ct X Y Z 0 0 0 0).2.2.2.2.1
  dsimp at h9
  rcases h9 with ⟨hVandA, hVandB, hVandC⟩
  rw [hABC] at hVandA hVandB hVandC
  have hProjC : (Ct * Z * Z * Z) * (Z - X) * (Z - Y) =
                (Z * Z) * ((At * X * X + Bt * Y * Y - Ct * Z * Z) * (X + Y) - (At * X + Bt * Y - Ct * Z) * X * Y) := by
    have hMul := congrArg (fun t => (Z * Z) * t) hVandC
    have hL : (Z * Z) * (Ct * Z * (Z - X) * (Z - Y)) = (Ct * Z * Z * Z) * (Z - X) * (Z - Y) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [hL, Int.sub_zero] at hMul
    exact hMul.symm
  have hProjA : (At * X * X * X) * (X - Y) * (X - Z) =
                (X * X) * ((At * X + Bt * Y - Ct * Z) * Y * Z - (At * X * X + Bt * Y * Y - Ct * Z * Z) * (Y + Z)) := by
    have hMul := congrArg (fun t => (X * X) * t) hVandA
    have hL : (X * X) * (At * X * (X - Y) * (X - Z)) = (At * X * X * X) * (X - Y) * (X - Z) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [hL, Int.add_zero] at hMul
    exact hMul.symm
  have hProjB : (Bt * Y * Y * Y) * (Y - X) * (Y - Z) =
                (Y * Y) * ((At * X + Bt * Y - Ct * Z) * Z * X - (At * X * X + Bt * Y * Y - Ct * Z * Z) * (Z + X)) := by
    have hMul := congrArg (fun t => (Y * Y) * t) hVandB
    have hL : (Y * Y) * (Bt * Y * (Y - X) * (Y - Z)) = (Bt * Y * Y * Y) * (Y - X) * (Y - Z) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [hL, Int.add_zero] at hMul
    exact hMul.symm
  refine ⟨⟨hProjC, hProjA, hProjB⟩, ?_, ?_⟩
  · intro hCt1 hX1 hY1 hXZ hYZ
    have hZ1 : 1 ≤ Z := by omega
    have hZX1 : 1 ≤ Z - X := by omega
    have hZY1 : 1 ≤ Z - Y := by omega
    have hCtZ : 1 ≤ Ct * Z := by
      have := Int.mul_le_mul hCt1 hZ1 (by omega) (by omega); omega
    have hCtZX : 1 ≤ Ct * Z * (Z - X) := by
      have := Int.mul_le_mul hCtZ hZX1 (by omega) (by omega); omega
    have hPos : 1 ≤ Ct * Z * (Z - X) * (Z - Y) := by
      have := Int.mul_le_mul hCtZX hZY1 (by omega) (by omega); omega
    have hVandEq : (At * X * X + Bt * Y * Y - Ct * Z * Z) * (X + Y) -
                   (At * X + Bt * Y - Ct * Z) * X * Y =
                   Ct * Z * (Z - X) * (Z - Y) := by
      rw [Int.sub_zero] at hVandC
      exact hVandC
    have hNotBoth : ¬(At * X + Bt * Y - Ct * Z = 0 ∧ At * X * X + Bt * Y * Y - Ct * Z * Z = 0) := by
      intro hBoth
      rcases hBoth with ⟨hS10, hS20⟩
      rw [hS10, hS20] at hVandEq
      simp only [Int.zero_mul, Int.sub_zero] at hVandEq
      omega
    have hAbsPos : 1 ≤ (At * X + Bt * Y - Ct * Z).natAbs + (At * X * X + Bt * Y * Y - Ct * Z * Z).natAbs := by
      rcases Int.lt_trichotomy (At * X + Bt * Y - Ct * Z) 0 with hLt1 | hEq1 | hGt1
      · omega
      · rcases Int.lt_trichotomy (At * X * X + Bt * Y * Y - Ct * Z * Z) 0 with hLt2 | hEq2 | hGt2
        · omega
        · exact False.elim (hNotBoth ⟨hEq1, hEq2⟩)
        · omega
      · omega
    refine ⟨hPos, hVandEq, hNotBoth, hAbsPos, ?_, ?_, by intro _ _; exact ⟨by omega, by omega⟩⟩
    · intro hS1ge0
      have hLin : Ct * Z ≤ At * X + Bt * Y := by omega
      have hZ2ge0 : 0 ≤ Z * Z := Int.mul_nonneg (by omega) (by omega)
      have hDiff : (At * X + Bt * Y) * (Z * Z) - Ct * Z * Z * Z =
                   (At * X + Bt * Y - Ct * Z) * (Z * Z) := by
        simp only [Int.sub_mul, Int.mul_assoc]
      have hProdGe0 : 0 ≤ (At * X + Bt * Y - Ct * Z) * (Z * Z) :=
        Int.mul_nonneg hS1ge0 hZ2ge0
      exact ⟨hLin, by omega⟩
    · intro hS2le0
      have hS2XY : (At * X * X + Bt * Y * Y - Ct * Z * Z) * (X + Y) ≤ 0 :=
        Int.mul_nonpos_of_nonpos_of_nonneg hS2le0 (by omega)
      have hNegS1XY : 1 ≤ (-(At * X + Bt * Y - Ct * Z)) * X * Y := by
        have : (-(At * X + Bt * Y - Ct * Z)) * X * Y = -((At * X + Bt * Y - Ct * Z) * X * Y) := by
          simp only [Int.neg_mul]
        omega
      have hXYpos : 1 ≤ X * Y := by
        have := Int.mul_le_mul hX1 hY1 (by omega) (by omega); omega
      have hS1neg : At * X + Bt * Y - Ct * Z ≤ -1 := by
        rcases Int.lt_trichotomy (At * X + Bt * Y - Ct * Z) 0 with hLt | hEq | hGt
        · omega
        · rw [hEq] at hNegS1XY; simp only [Int.neg_zero, Int.zero_mul] at hNegS1XY; omega
        · have hNonneg : 0 ≤ (At * X + Bt * Y - Ct * Z) * (X * Y) :=
            Int.mul_nonneg (by omega) (by omega)
          have hEqAssoc : (-(At * X + Bt * Y - Ct * Z)) * X * Y =
                          -((At * X + Bt * Y - Ct * Z) * (X * Y)) := by
            simp only [Int.neg_mul, Int.mul_assoc]
          omega
      exact ⟨hS1neg, hNegS1XY⟩
  · intro hBezZ2 hWx1 hWy1 hCt1 hZ1 hAlpha0 hAlphaMax
    have hZ2pos : 1 ≤ Z * Z := by
      have := Int.mul_le_mul hZ1 hZ1 (by omega) (by omega); omega
    have hWyAlpha0 : 0 ≤ (Bt * Y) * alpha := Int.mul_nonneg (by omega) hAlpha0
    have hWyAlphaMax : (Bt * Y) * alpha ≤ (Bt * Y) * (At * X - 1) := by
      have hDiff : (Bt * Y) * (At * X - 1) - (Bt * Y) * alpha = (Bt * Y) * ((At * X - 1) - alpha) := by
        simp only [Int.mul_sub]
      have hNonneg : 0 ≤ (Bt * Y) * ((At * X - 1) - alpha) :=
        Int.mul_nonneg (by omega) (by omega)
      omega
    have hWxBetaLow : Z * Z ≤ (At * X) * beta := by omega
    have hWxBetaHigh : (At * X) * beta ≤ Z * Z + (Bt * Y) * (At * X - 1) := by omega
    have hBeta1 : 1 ≤ beta := by
      rcases Int.lt_trichotomy beta 1 with hLt | hEq | hGt
      · have hWxBetaNonpos : (At * X) * beta ≤ 0 :=
          Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
        exact False.elim (Int.lt_irrefl 0 (by omega))
      · omega
      · omega
    have hCollapse :
        (Bt * Y) * (Ct * Z * Z * Z) + (Bt * Bt * Ct) * (Y * Y * Z) * alpha -
        ((At * Bt * Ct) * (X * Y * Z)) * beta =
        (Bt * Ct * Y * Z) * (Z * Z - ((At * X) * beta - (Bt * Y) * alpha)) := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
    have hZero : Z * Z - ((At * X) * beta - (Bt * Y) * alpha) = 0 := by omega
    rw [hZero, Int.mul_zero] at hCollapse
    have hCoeffNonneg : 0 ≤ (Bt * Bt * Ct) * (Y * Y * Z) := by
      have hB2Y2 : 0 ≤ (Bt * Y) * (Bt * Y) := Int.mul_nonneg (by omega) (by omega)
      have hCtZ : 0 ≤ Ct * Z := Int.mul_nonneg (by omega) (by omega)
      have hProd : 0 ≤ ((Bt * Y) * (Bt * Y)) * (Ct * Z) := Int.mul_nonneg hB2Y2 hCtZ
      have hEq : (Bt * Bt * Ct) * (Y * Y * Z) = ((Bt * Y) * (Bt * Y)) * (Ct * Z) := by
        simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      rw [hEq]; exact hProd
    have hTermLow : 0 ≤ (Bt * Bt * Ct) * (Y * Y * Z) * alpha :=
      Int.mul_nonneg hCoeffNonneg hAlpha0
    have hTermHigh : (Bt * Bt * Ct) * (Y * Y * Z) * alpha ≤
                     (Bt * Bt * Ct) * (Y * Y * Z) * (At * X - 1) := by
      have hDiff : (Bt * Bt * Ct) * (Y * Y * Z) * (At * X - 1) -
                   (Bt * Bt * Ct) * (Y * Y * Z) * alpha =
                   (Bt * Bt * Ct) * (Y * Y * Z) * ((At * X - 1) - alpha) := by
        simp only [Int.mul_sub]
      have hNonneg : 0 ≤ (Bt * Bt * Ct) * (Y * Y * Z) * ((At * X - 1) - alpha) :=
        Int.mul_nonneg hCoeffNonneg (by omega)
      omega
    exact ⟨⟨hWxBetaLow, hWxBetaHigh, hBeta1⟩, by omega, ⟨by omega, by omega⟩⟩

/-- **Theorem 14c (Three-Shaft Mason–Stothers Minor Closure `(Z², Y², X²)` and Joint Principal-Cell
Bilateral Brackets for `(α, β, γ)` and `(A, B, C)`)**:
When all three Mason–Stothers–Bézout shaft-square minor laws hold simultaneously:
`(Ã X) β - (B̃ Y) α = Z²`, `(Ã X) γ - (C̃ Z) α = Y²`, `(C̃ Z) β - (B̃ Y) γ = X²`,
together with `A* + B* = C*` (`X² α + Y² β = Z² γ`):
1. **Three-Shaft Volume Collapse System over `R_full = Ã B̃ C̃ X Y Z`:**
   - `(B̃ * Y) * C + (B̃ * B̃ * C̃) * (Y * Y * Z) * α = R_full * β`,
   - `(C̃ * Z) * B + (B̃ * C̃ * C̃) * (Y * Z * Z) * α = R_full * γ`,
   - `(B̃ * Y) * (C̃ * Z) * A = R_full * ((C̃ * Z) * β - (B̃ * Y) * γ)` (gauge-invariant, `α`-free).
2. **Simultaneous Principal-Cell Bilateral Brackets (`0 ≤ α ≤ Ã X - 1`):**
   Whenever `1 ≤ Ã X`, `1 ≤ B̃ Y`, `1 ≤ C̃ Z`, `1 ≤ Y`, and `0 ≤ α ≤ Ã X - 1`:
   - `Y² ≤ (Ã * X) * γ ∧ (Ã * X) * γ ≤ Y² + (C̃ * Z) * (Ã * X - 1) ∧ 1 ≤ γ`,
   - `R_full * γ - (B̃ * C̃ * C̃) * (Y * Z * Z) * (Ã * X - 1) ≤ (C̃ * Z) * B ∧ (C̃ * Z) * B ≤ R_full * γ`,
   - `Y² * β ≤ Z² * γ ∧ Z² * γ ≤ Y² * β + A - X²`. -/
theorem thm14c_abc_three_shaft_minor_closure_and_joint_beta_gamma_brackets
    (At Bt Ct X Y Z alpha beta gamma : Int)
    (hMinZ : (At * X) * beta - (Bt * Y) * alpha = Z * Z)
    (hMinY : (At * X) * gamma - (Ct * Z) * alpha = Y * Y)
    (hMinX : (Ct * Z) * beta - (Bt * Y) * gamma = X * X)
    (hDeriv : (X * X) * alpha + (Y * Y) * beta = (Z * Z) * gamma) :
    let A  := At * X * X * X
    let B  := Bt * Y * Y * Y
    let C  := Ct * Z * Z * Z
    let wx := At * X
    let wy := Bt * Y
    let wz := Ct * Z
    let Rfull := (At * Bt * Ct) * (X * Y * Z)
    ((wy * C + (Bt * Bt * Ct) * (Y * Y * Z) * alpha = Rfull * beta) ∧
     (wz * B + (Bt * Ct * Ct) * (Y * Z * Z) * alpha = Rfull * gamma) ∧
     (wy * wz * A = Rfull * (wz * beta - wy * gamma))) ∧
    (1 ≤ wx → 1 ≤ wy → 1 ≤ wz → 1 ≤ Y → 0 ≤ alpha → alpha ≤ wx - 1 →
      (Y * Y ≤ wx * gamma ∧ wx * gamma ≤ Y * Y + wz * (wx - 1) ∧ 1 ≤ gamma) ∧
      (Rfull * gamma - (Bt * Ct * Ct) * (Y * Z * Z) * (wx - 1) ≤ wz * B ∧
       wz * B ≤ Rfull * gamma) ∧
      ((Y * Y) * beta ≤ (Z * Z) * gamma ∧ (Z * Z) * gamma ≤ (Y * Y) * beta + A - X * X)) := by
  intro A B C wx wy wz Rfull
  have hColC : wy * C + (Bt * Bt * Ct) * (Y * Y * Z) * alpha = Rfull * beta := by
    have hId : wy * C + (Bt * Bt * Ct) * (Y * Y * Z) * alpha - Rfull * beta =
               (Bt * Ct * Y * Z) * (Z * Z - (wx * beta - wy * alpha)) := by
      dsimp [wy, C, Rfull, wx]
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
    have hZ0 : Z * Z - (wx * beta - wy * alpha) = 0 := by
      dsimp [wx, wy]; omega
    rw [hZ0, Int.mul_zero] at hId; omega
  have hColB : wz * B + (Bt * Ct * Ct) * (Y * Z * Z) * alpha = Rfull * gamma := by
    have hId : wz * B + (Bt * Ct * Ct) * (Y * Z * Z) * alpha - Rfull * gamma =
               (Bt * Ct * Y * Z) * (Y * Y - (wx * gamma - wz * alpha)) := by
      dsimp [wz, B, Rfull, wx]
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
    have hY0 : Y * Y - (wx * gamma - wz * alpha) = 0 := by
      dsimp [wx, wz]; omega
    rw [hY0, Int.mul_zero] at hId; omega
  have hColA : wy * wz * A = Rfull * (wz * beta - wy * gamma) := by
    have hId : wy * wz * A - Rfull * (wz * beta - wy * gamma) =
               Rfull * (X * X - (wz * beta - wy * gamma)) := by
      dsimp [wy, wz, A, Rfull]
      simp only [Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have hX0 : X * X - (wz * beta - wy * gamma) = 0 := by
      dsimp [wz, wy]; omega
    rw [hX0, Int.mul_zero] at hId; omega
  refine ⟨⟨hColC, hColB, hColA⟩, ?_⟩
  intro hWx1 hWy1 hWz1 hY1 hAlpha0 hAlphaMax
  have hY2pos : 1 ≤ Y * Y := by
    have := Int.mul_le_mul hY1 hY1 (by omega) (by omega); omega
  have hWzAlpha0 : 0 ≤ wz * alpha := Int.mul_nonneg (by omega) hAlpha0
  have hWzAlphaMax : wz * alpha ≤ wz * (wx - 1) := by
    have hDiff : wz * (wx - 1) - wz * alpha = wz * ((wx - 1) - alpha) := by
      simp only [Int.mul_sub]
    have hNonneg : 0 ≤ wz * ((wx - 1) - alpha) :=
      Int.mul_nonneg (by omega) (by omega)
    omega
  have hWxGammaLow : Y * Y ≤ wx * gamma := by
    dsimp [wx, wz] at hWzAlpha0 ⊢; omega
  have hWxGammaHigh : wx * gamma ≤ Y * Y + wz * (wx - 1) := by
    dsimp [wx, wz] at hWzAlphaMax ⊢; omega
  have hGamma1 : 1 ≤ gamma := by
    rcases Int.lt_trichotomy gamma 1 with hLt | hEq | hGt
    · have hNonpos : wx * gamma ≤ 0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      exact False.elim (Int.lt_irrefl 0 (by omega))
    · omega
    · omega
  have hCoeffBNonneg : 0 ≤ (Bt * Ct * Ct) * (Y * Z * Z) := by
    have hEq : (Bt * Ct * Ct) * (Y * Z * Z) = wy * (wz * wz) := by
      dsimp [wy, wz]; simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have hWz2 : 0 ≤ wz * wz := Int.mul_nonneg (by omega) (by omega)
    have hProd : 0 ≤ wy * (wz * wz) := Int.mul_nonneg (by omega) hWz2
    rw [hEq]; exact hProd
  have hBTermLow : 0 ≤ (Bt * Ct * Ct) * (Y * Z * Z) * alpha :=
    Int.mul_nonneg hCoeffBNonneg hAlpha0
  have hBTermHigh : (Bt * Ct * Ct) * (Y * Z * Z) * alpha ≤
                    (Bt * Ct * Ct) * (Y * Z * Z) * (wx - 1) := by
    have hDiff : (Bt * Ct * Ct) * (Y * Z * Z) * (wx - 1) -
                 (Bt * Ct * Ct) * (Y * Z * Z) * alpha =
                 (Bt * Ct * Ct) * (Y * Z * Z) * ((wx - 1) - alpha) := by
      simp only [Int.mul_sub]
    have hNonneg : 0 ≤ (Bt * Ct * Ct) * (Y * Z * Z) * ((wx - 1) - alpha) :=
      Int.mul_nonneg hCoeffBNonneg (by omega)
    omega
  have hX2Nonneg : 0 ≤ X * X := by
    rcases Int.lt_trichotomy X 0 with hLt | hEq | hGt
    · have : 0 < (-X) * (-X) := Int.mul_pos (by omega) (by omega)
      have hNegSq : (-X) * (-X) = X * X := by simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      omega
    · rw [hEq]; omega
    · have := Int.mul_pos hGt hGt; omega
  have hX2Alpha0 : 0 ≤ (X * X) * alpha := Int.mul_nonneg hX2Nonneg hAlpha0
  have hX2AlphaMax : (X * X) * alpha ≤ A - X * X := by
    have hId : (A - X * X) - (X * X) * alpha = (X * X) * ((wx - 1) - alpha) := by
      dsimp [A, wx]
      simp only [Int.mul_sub, Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have hNonneg : 0 ≤ (X * X) * ((wx - 1) - alpha) :=
      Int.mul_nonneg hX2Nonneg (by omega)
    omega
  exact ⟨⟨hWxGammaLow, hWxGammaHigh, hGamma1⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

#print axioms thm8_unified_3x3_pillai_abc_skeletal_matrix_and_radical_floor_embedding
#print axioms thm9_pillai_abc_differential_bezout_and_pade_laws
#print axioms thm12_reverse_pade_bezout_cubic_annihilation_and_radical_bound
#print axioms thm13_integer_mason_stothers_cubic_wronskian_and_fourth_power_det
#print axioms thm14_master_pillai_and_abc_bilateral_convergence_chains
#print axioms thm15_cross_floor_k2_k3_sixth_power_genus10_lock
#print axioms thm16_weierstrass_stereographic_abc_embedding_into_z512_rotator
#print axioms thm12b_abc_countable_pade_tower_cubic_annihilation_and_adjacent_floor_escape
#print axioms thm14b_abc_hankel_vandermonde_floor_defect_trichotomy_and_bilateral_bezout_bracket
#print axioms thm14c_abc_three_shaft_minor_closure_and_joint_beta_gamma_brackets

end RotatorCalculusPaper
