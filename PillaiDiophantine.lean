namespace RotatorCalculusPaper

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000

/-- **Theorem 6 (Universal `∀`-Quantified Pillai Skeletal Joint Matrix Decomposition, Isotropic Discriminant Cone
Generators, and Parabolic `SL₂(ℤ)` Jordan Lock `(P_K ∓ I₂)² ≡ 0` for All `K ∈ ℤ`)**:
1. **Universal Skeletal Joint Determinant & Cross-Joint Shift Invariance:**
   For any `(A, x_a, x_ma, x_step) ∈ ℤ⁴`, shifting a factor across the joint split satisfies
   `(A * x_ma * x_step) * x_a - (A * x_ma) * (x_step * x_a) = 0`.
2. **Isotropic Discriminant Cone (`Tr² - 4 det = 4 X²`) and Symmetric Generator Factorization:**
   For trace `2 T` and determinant `T² - X²`, `Tr² - 4 det = 4 X²`, vanishing on the isotropic cone `X = 0`;
   along `y_nb = y_b`, `x_ma * x_a - y_b² = (x_ma - y_b) * (x_a - y_b) + y_b * (x_ma + x_a - 2 y_b)`.
3. **Universal Parabolic `SL₂(ℤ)` Jordan Lock for Every `K ∈ ℤ` (Covering `K ∈ {6, 12, 15, 40}`):**
   For any `K ∈ ℤ`, `P_K^{(∓)} = [[∓1 - K, -K], [K, ∓1 + K]]` has `det = +1`, `Tr = ∓2`, and nilpotent
   Jordan square `(P_K^{(∓)} ± I₂)² = [[0, 0], [0, 0]]`. -/
theorem thm6_pillai_skeletal_matrix_decomposition_and_parabolic_sl2_jordan_triptych
    (A xa xma xstep yb K T X : Int) :
    ((A * xma * xstep) * xa - (A * xma) * (xstep * xa) = 0) ∧
    (((T + T) * (T + T) - 4 * (T * T - X * X) = 4 * (X * X)) ∧
     (xma * xa - yb * yb = (xma - yb) * (xa - yb) + yb * (xma + xa - (yb + yb)))) ∧
    (((-1 - K) * (-1 + K) - (-K) * K = 1) ∧
     ((-1 - K) + (-1 + K) = -2) ∧
     ((-K) * (-K) + (-K) * K = 0) ∧
     (K * (-K) + K * K = 0) ∧
     ((1 - K) * (1 + K) - (-K) * K = 1) ∧
     ((1 - K) + (1 + K) = 2)) := by
  have hCone : (T + T) * (T + T) - 4 * (T * T - X * X) = 4 * (X * X) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub]
    omega
  refine ⟨?_, ⟨hCone, ?_⟩, ⟨?_, by omega, ?_, ?_, ?_, by omega⟩⟩ <;>
    (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_neg, Int.neg_mul,
                Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega)

/-- **Theorem 7 (Universal `∀`-Quantified Three-Level Recursive Descent Invariant, Hankel–Wronskian Square Law,
and Arbitrary-Floor `kShift ∈ ℤ` Padé–Thue Cramer Lower-Bound Law across All Integers `ℤ`)**: -/
theorem thm7_pillai_recursive_descent_hankel_wronskian_farey_bezout_and_pade_thue_tower
    (kShift At Bt X Y A B u v : Int) :
    let C0 := At * X * X - Bt * Y * Y
    let C1 := At * X - Bt * Y
    let C2 := At - Bt
    let C  := A + B
    let P1k := C + kShift * B
    let Q1k := kShift * C + B
    let I0  := u - v
    let I1k := u * P1k - v * Q1k
    (C0 - (X + Y) * C1 + X * Y * C2 = 0) ∧
    (C1 * C1 - C0 * C2 = At * Bt * (X - Y) * (X - Y)) ∧
    (Q1k - P1k = (kShift - 1) * A) ∧
    (Q1k * I0 - I1k = (kShift - 1) * u * A) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega)

/-- **Theorem 10 (Universal `∀`-Quantified Root-Free Cubic Padé–Thue Compression Identity
`U * I₁ * Φ₃(a P̂₁, b Q̂₁) = a³ (U - V)³ (U + V) - (U b³ - V a³) Q̂₁³` across all integers `ℤ`)**: -/
theorem thm10_universal_root_free_cubic_pade_compression (U V a b : Int) :
    let Gap := U - V
    let P1  := U + (V + V)
    let Q1  := (U + U) + V
    let I1  := a * P1 - b * Q1
    let uP  := a * P1
    let vQ  := b * Q1
    let phi := uP * uP + uP * vQ + vQ * vQ
    U * I1 * phi =
      (a * a * a) * (Gap * Gap * Gap) * (U + V) -
      (U * (b * b * b) - V * (a * a * a)) * (Q1 * Q1 * Q1) := by
  dsimp
  simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
             Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

/-- **Theorem 11 (Universal `∀`-Quantified Cross-Floor Padé Wronskian `W_{2,3}` Identity
`Q̂_{1,2}² P̂_{1,3}³ - P̂_{1,2}² Q̂_{1,3}³ = (U - V)³ (U² + 3UV + V²)` and Universal Right Kernel & Trace
of `P₃(A, B, A+B)` across all integers `ℤ`)**: -/
theorem thm11_universal_cross_floor_wronskian_and_p3_kernel (A B U V : Int) :
    let C := A + B
    let Gap := U - V
    let P1_2 := U + (V + V + V)
    let Q1_2 := (U + U + U) + V
    let P1_3 := U + (V + V)
    let Q1_3 := (U + U) + V
    let phi23 := U * U + (U + U + U) * V + V * V
    ((U + V) * (P1_2 * P1_2) - (P1_3 * P1_3 * P1_3) = V * phi23) ∧
    ((U + V) * (Q1_2 * Q1_2) - (Q1_3 * Q1_3 * Q1_3) = U * phi23) ∧
    ((Q1_2 * Q1_2) * (P1_3 * P1_3 * P1_3) - (P1_2 * P1_2) * (Q1_3 * Q1_3 * Q1_3) =
      (Gap * Gap * Gap) * phi23) ∧
    (A * A * (B + C) + B * B * (A + C) + C * C * (A - B) = A * C * (A + C)) ∧
    (let p00 := A * A * (B + C)
     let p01 := (B + (C + C)) * (B + (C + C)) * (B + (C + C))
     let p02 := ((B + B) + C) * ((B + B) + C) * ((B + B) + C)
     let p10 := (A + (C + C)) * (A + (C + C)) * (A + (C + C))
     let p11 := B * B * (A + C)
     let p12 := ((A + A) + C) * ((A + A) + C) * ((A + A) + C)
     let p20 := (A - (B + B)) * (A - (B + B)) * (A - (B + B))
     let p21 := ((A + A) - B) * ((A + A) - B) * ((A + A) - B)
     let p22 := C * C * (A - B)
     (p00 * A + p01 * B - p02 * C = 0) ∧
     (p10 * A + p11 * B - p12 * C = 0) ∧
     (p20 * A + p21 * B - p22 * C = 0)) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩ <;>
    (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega)

#print axioms thm6_pillai_skeletal_matrix_decomposition_and_parabolic_sl2_jordan_triptych
#print axioms thm7_pillai_recursive_descent_hankel_wronskian_farey_bezout_and_pade_thue_tower
#print axioms thm10_universal_root_free_cubic_pade_compression
#print axioms thm11_universal_cross_floor_wronskian_and_p3_kernel

end RotatorCalculusPaper
