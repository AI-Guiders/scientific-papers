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

/-- **Theorem 14 (Exact Volume–Wronskian–Radical Defect Identities and `3 × 3` Cubic Cramer–Bézout Laws (`0 non-order Prop premises`)**: -/
theorem thm14_master_pillai_and_abc_bilateral_convergence_chains
    (At Bt Ct X Y Z u0 v0 t U0 V0 U1 V1 : Int) :
    let wx := At * X
    let wy := Bt * Y
    let dBezMS := wx * v0 - wy * u0
    let alpha := u0 * (Z * Z) + t * wx
    let beta  := v0 * (Z * Z) + t * wy
    let A  := At * X * X * X
    let B  := Bt * Y * Y * Y
    let C  := Ct * Z * Z * Z
    let S3 := A + B - C
    let As := (X * X) * alpha
    let Bs := (Y * Y) * beta
    let Rfull := (At * Bt * Ct) * (X * Y * Z)
    let X3 := X * X * X
    let Y3 := Y * Y * Y
    let Z3 := Z * Z * Z
    let e0 := U0 * Y3 - V0 * X3 - 1
    let e1 := V1 * Z3 - U1 * Y3 - 1
    let Dcube := At * U0 * V1 + Bt * V0 * V1 - Ct * U1 * V0
    (dBezMS * (A * B * C) = Rfull * (A * Bs - B * As)) ∧
    (dBezMS * wy * C + (Bt * Bt * Ct) * (Y * Y * Z) * alpha = Rfull * beta) ∧
    (Rfull * Rfull * Rfull - C = C * (((At * Bt * Ct) * (At * Bt * Ct)) * A * B - 1)) ∧
    ((Dcube * X3 - (Ct * (U0 + U1) - Bt * V1) =
        U0 * V1 * S3 - (Bt * V1 - Ct * U1) * e0 + Ct * U0 * e1) ∧
     (Dcube * Y3 - (At * V1 + Ct * V0) =
        V0 * V1 * S3 + At * V1 * e0 + Ct * V0 * e1) ∧
     (Dcube * Z3 - (At * (U0 + U1) + Bt * V0) =
        U1 * V0 * S3 + At * U1 * e0 + (At * U0 + Bt * V0) * e1)) := by
  dsimp
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩ <;>
    (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                Int.mul_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_one, Int.one_mul]; try omega)

/-- **Theorem 15 (Cross-Floor Locking Identity `k = 2 ↔ k = 3 ⟹ K = 6`
of Genus `g(6) = 10 ≥ 2` and Euler Characteristic Trichotomy `χ(C_k) = k(3 - k)`, `0 Prop premises`)**: -/
theorem thm15_cross_floor_k2_k3_sixth_power_genus10_lock
    (A2 B2 C2 X2 Y2 Z2 A3 B3 C3 X3 Y3 Z3 k : Int) :
    let A := A2 * (X2 * X2)
    let B := B2 * (Y2 * Y2)
    let C := C2 * (Z2 * Z2)
    let dA := A - A3 * (X3 * X3 * X3)
    let dB := B - B3 * (Y3 * Y3 * Y3)
    let dC := C - C3 * (Z3 * Z3 * Z3)
    let S := A + B - C
    let V6 := Y2 * X3 * Z3
    let W6 := Z2 * X3 * Y3
    ((A2 * A2 * A2) * (X2 * X2 * X2 * X2 * X2 * X2) -
     A * (A3 * A3) * (X3 * X3 * X3 * X3 * X3 * X3) =
     A * dA * (A + A3 * (X3 * X3 * X3))) ∧
    ((B2 * B2 * B2) * (Y2 * Y2 * Y2 * Y2 * Y2 * Y2) -
     B * (B3 * B3) * (Y3 * Y3 * Y3 * Y3 * Y3 * Y3) =
     B * dB * (B + B3 * (Y3 * Y3 * Y3))) ∧
    ((C2 * C2 * C2) * (Z2 * Z2 * Z2 * Z2 * Z2 * Z2) -
     C * (C3 * C3) * (Z3 * Z3 * Z3 * Z3 * Z3 * Z3) =
     C * dC * (C + C3 * (Z3 * Z3 * Z3))) ∧
    ((A * (A3 * A3) * (X3 * X3 * X3 * X3 * X3 * X3)) *
       ((B3 * B3) * (C3 * C3) * (Y3 * Y3 * Y3 * Y3 * Y3 * Y3) * (Z3 * Z3 * Z3 * Z3 * Z3 * Z3)) +
     (B * (B3 * B3) * (Y3 * Y3 * Y3 * Y3 * Y3 * Y3)) *
       ((A3 * A3) * (C3 * C3) * (X3 * X3 * X3 * X3 * X3 * X3) * (Z3 * Z3 * Z3 * Z3 * Z3 * Z3)) -
     (C * (C3 * C3) * (Z3 * Z3 * Z3 * Z3 * Z3 * Z3)) *
       ((A3 * A3) * (B3 * B3) * (X3 * X3 * X3 * X3 * X3 * X3) * (Y3 * Y3 * Y3 * Y3 * Y3 * Y3)) =
     S * ((A3 * A3) * (B3 * B3) * (C3 * C3) *
       (X3 * X3 * X3 * X3 * X3 * X3) * (Y3 * Y3 * Y3 * Y3 * Y3 * Y3) * (Z3 * Z3 * Z3 * Z3 * Z3 * Z3))) ∧
    (W6 * W6 * W6 * W6 * W6 * V6 + W6 * W6 * W6 * W6 * W6 * (W6 - V6) =
     W6 * W6 * W6 * W6 * W6 * W6) ∧
    (2 - (k - 1) * (k - 2) = k * (3 - k)) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)

/-- **Theorem 16 (Weierstrass Stereographic Embedding of `C := A + B ∈ ℤ`
into a Four-Quadrant Rotator `ℤ_{4Q}`, `0 Prop premises`)**: -/
theorem thm16_weierstrass_stereographic_abc_embedding_into_z512_rotator
    (Q A B u v phi0 : Int) :
    let C := A + B
    let w := u + v
    let dBez := A * v - B * u
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
    (C * Drot - w * Irot = Q * dBez) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega)

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
                 R kShift Ct Bt Z Y w v
  dsimp at h10b
  rcases h10b with ⟨_, hGenCube, _, hCancelZ3, hFloor3, _, hEscape⟩
  exact ⟨⟨hDiff, hSum⟩, hFloor3, hGenCube, hCancelZ3, hStep, hNondeg, hEscape⟩

/-- **Theorem 14b (Lagrange–Vandermonde Floor-Defect Projectors `(S₁, S₂, S₃)`
and Principal-Cell Bilateral Bézout Height Bracket, `0 Prop premises`)**: -/
theorem thm14b_abc_hankel_vandermonde_floor_defect_trichotomy_and_bilateral_bezout_bracket
    (At Bt Ct X Y Z alpha beta : Int) :
    let A  := At * X * X * X
    let B  := Bt * Y * Y * Y
    let C  := Ct * Z * Z * Z
    let S1 := At * X + Bt * Y - Ct * Z
    let S2 := At * X * X + Bt * Y * Y - Ct * Z * Z
    let S3 := A + B - C
    let wx := At * X
    let wy := Bt * Y
    let dMinZ := (Z * Z) - (wx * beta - wy * alpha)
    let Rfull := (At * Bt * Ct) * (X * Y * Z)
    ((C * (Z - X) * (Z - Y) = (Z * Z) * (S2 * (X + Y) - S1 * X * Y - S3)) ∧
     (A * (X - Y) * (X - Z) = (X * X) * (S1 * Y * Z - S2 * (Y + Z) + S3)) ∧
     (B * (Y - X) * (Y - Z) = (Y * Y) * (S1 * Z * X - S2 * (Z + X) + S3))) ∧
    ((At * X + Bt * Y) * (Z * Z) - C = S1 * (Z * Z)) ∧
    (wy * C + (Bt * Bt * Ct) * (Y * Y * Z) * alpha - Rfull * beta =
     (Bt * Ct * Y * Z) * dMinZ) := by
  dsimp
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)

/-- **Theorem 14c (Three-Shaft Mason–Stothers Minor Defect Identities `(dMinZ, dMinY, dMinX)`
over `R_full = Ã B̃ C̃ X Y Z`, `0 Prop premises`)**: -/
theorem thm14c_abc_three_shaft_minor_closure_and_joint_beta_gamma_brackets
    (At Bt Ct X Y Z alpha beta gamma : Int) :
    let A  := At * X * X * X
    let B  := Bt * Y * Y * Y
    let C  := Ct * Z * Z * Z
    let wx := At * X
    let wy := Bt * Y
    let wz := Ct * Z
    let Rfull := (At * Bt * Ct) * (X * Y * Z)
    let dMinZ := Z * Z - (wx * beta - wy * alpha)
    let dMinY := Y * Y - (wx * gamma - wz * alpha)
    let dMinX := X * X - (wz * beta - wy * gamma)
    (wy * C + (Bt * Bt * Ct) * (Y * Y * Z) * alpha - Rfull * beta =
     (Bt * Ct * Y * Z) * dMinZ) ∧
    (wz * B + (Bt * Ct * Ct) * (Y * Z * Z) * alpha - Rfull * gamma =
     (Bt * Ct * Y * Z) * dMinY) ∧
    (wy * wz * A - Rfull * (wz * beta - wy * gamma) = Rfull * dMinX) ∧
    ((A - X * X) - (X * X) * alpha = (X * X) * ((wx - 1) - alpha)) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                Int.mul_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_one, Int.one_mul]; try omega)

end RotatorCalculusPaper
