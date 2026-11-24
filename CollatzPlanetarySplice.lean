namespace RotatorCalculusPaper

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000

/-- **Theorem 18 (Universal Two-Arc Pillai–Wronskian Trajectory Composition & Cycle Chord Law)**:
For any two consecutive binary–ternary trajectory arcs `P₁ n_mid - Q₁ n_start = D₁` and
`P₂ n_final - Q₂ n_mid = D₂` (`C₁ = P₁ - Q₁`, `C₂ = P₂ - Q₂`, `C_tot = P₁ P₂ - Q₁ Q₂`,
`D_tot = Q₂ D₁ + P₁ D₂`), the composite displacement decomposes in `ℤ_{C_tot}` as
`(P₁ P₂)(n_final - n_start) + C_tot n_start = D_tot`, and on any closed cycle (`n_final = n_start`)
the chord displacement is locked to the `2 × 2` Wronskian determinant:
`C_tot (n_mid - n_start) = C₂ D₁ - C₁ D₂`. -/
theorem thm18_universal_arbitrary_modulus_rotator_and_two_arc_trajectory_wronskian
    (P1 Q1 P2 Q2 n_start n_mid n_final D1 D2 : Int)
    (hArc1 : P1 * n_mid - Q1 * n_start = D1)
    (hArc2 : P2 * n_final - Q2 * n_mid = D2) :
    let C1 := P1 - Q1
    let C2 := P2 - Q2
    let Ctot := P1 * P2 - Q1 * Q2
    let Dtot := Q2 * D1 + P1 * D2
    ((P1 * P2) * n_final - (Q1 * Q2) * n_start = Dtot) ∧
    (Ctot = Q2 * C1 + P1 * C2) ∧
    (Ctot = P2 * C1 + Q1 * C2) ∧
    ((P1 * P2) * (n_final - n_start) + Ctot * n_start = Dtot) ∧
    ((Q1 * Q2) * (n_final - n_start) + Ctot * n_final = Dtot) ∧
    ((P1 * P2) * (n_mid - n_start) + (P2 * C1) * n_start = P2 * D1) ∧
    (n_final = n_start →
      (Ctot * n_start = Q2 * D1 + P1 * D2) ∧
      (Ctot * n_mid   = P2 * D1 + Q1 * D2) ∧
      (Ctot * (n_mid - n_start) = C2 * D1 - C1 * D2)) := by
  dsimp
  have hComp : ((P1 * P2) * n_final - (Q1 * Q2) * n_start) - (Q2 * D1 + P1 * D2) =
               Q2 * (P1 * n_mid - Q1 * n_start - D1) + P1 * (P2 * n_final - Q2 * n_mid - D2) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hC1 : (P1 * P2 - Q1 * Q2) - (Q2 * (P1 - Q1) + P1 * (P2 - Q2)) = 0 := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hC2 : (P1 * P2 - Q1 * Q2) - (P2 * (P1 - Q1) + Q1 * (P2 - Q2)) = 0 := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hDisp1 : ((P1 * P2) * (n_final - n_start) + (P1 * P2 - Q1 * Q2) * n_start) -
                ((P1 * P2) * n_final - (Q1 * Q2) * n_start) = 0 := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hDisp2 : ((Q1 * Q2) * (n_final - n_start) + (P1 * P2 - Q1 * Q2) * n_final) -
                ((P1 * P2) * n_final - (Q1 * Q2) * n_start) = 0 := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hMidDisp : ((P1 * P2) * (n_mid - n_start) + (P2 * (P1 - Q1)) * n_start) - P2 * D1 =
                  P2 * (P1 * n_mid - Q1 * n_start - D1) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hCycMid : ((P1 * P2 - Q1 * Q2) * n_mid) - (P2 * D1 + Q1 * D2) =
                 P2 * (P1 * n_mid - Q1 * n_start - D1) + Q1 * (P2 * n_final - Q2 * n_mid - D2) -
                 (Q1 * P2) * (n_final - n_start) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hWronsk : ((P1 * P2 - Q1 * Q2) * (n_mid - n_start)) - ((P2 - Q2) * D1 - (P1 - Q1) * D2) =
                 (P2 - Q2) * (P1 * n_mid - Q1 * n_start - D1) +
                 (Q1 - P1) * (P2 * n_final - Q2 * n_mid - D2) -
                 ((Q1 - P1) * P2) * (n_final - n_start) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have e1 : P1 * n_mid - Q1 * n_start - D1 = 0 := by omega
  have e2 : P2 * n_final - Q2 * n_mid - D2 = 0 := by omega
  rw [e1] at hMidDisp
  rw [e1, e2] at hComp hCycMid hWronsk
  simp only [Int.mul_zero, Int.add_zero, Int.zero_add] at hComp hMidDisp hCycMid hWronsk
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  intro hCycle
  have e3 : n_final - n_start = 0 := by omega
  rw [e3] at hDisp1 hCycMid hWronsk
  simp only [Int.mul_zero, Int.zero_add, Int.sub_zero] at hDisp1 hCycMid hWronsk
  exact ⟨by omega, by omega, by omega⟩

/-- **Theorem 19 (Unimodular `SL₂(ℤ)` Catalan Exponent-Basis Decomposition `u = 2a - 3b, v = 2b - a`
and Sign-Free Strictly Positive Cycle Wronskian Sum)**: -/
theorem thm19_collatz_catalan_sl2_basis_drift_bounds_and_positive_wronskian_sum
    (a b P1 Q1 P2 Q2 n_start n_mid n_final D1 D2 : Int) :
    let u := 2 * a - 3 * b
    let v := 2 * b - a
    let G1 := P1 - Q1
    let G2 := Q2 - P2
    let Ctot := P1 * P2 - Q1 * Q2
    (2 * 2 - 3 * 1 = 1 ∧ 2 * u + 3 * v = a ∧ u + 2 * v = b ∧ u + v = a - b ∧
     (2 * a > 3 * b ∧ 2 * b > a → u ≥ 1 ∧ v ≥ 1)) ∧
    (Ctot = P2 * G1 - Q1 * G2 ∧ Ctot = Q2 * G1 - P1 * G2) ∧
    (P1 * n_mid - Q1 * n_start = D1 → P2 * n_final - Q2 * n_mid = D2 → n_final = n_start →
      (Ctot * (n_start - n_mid) = G2 * D1 + G1 * D2) ∧
      (G1 ≥ 1 → G2 ≥ 1 → D1 ≥ 1 → D2 ≥ 1 →
        G2 * D1 + G1 * D2 ≥ 2 ∧ Ctot * (n_start - n_mid) ≥ G2 * D1 + 1 ∧ Ctot * (n_start - n_mid) ≥ G1 * D2 + 1) ∧
      (Ctot > 0 → G2 * D1 + G1 * D2 > 0 → n_start > n_mid)) := by
  dsimp
  have hSplit1 : (P1 * P2 - Q1 * Q2) - (P2 * (P1 - Q1) - Q1 * (Q2 - P2)) = 0 := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hSplit2 : (P1 * P2 - Q1 * Q2) - (Q2 * (P1 - Q1) - P1 * (Q2 - P2)) = 0 := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  refine ⟨⟨by omega, by omega, by omega, by omega, by intro _; exact ⟨by omega, by omega⟩⟩, ⟨by omega, by omega⟩, ?_⟩
  intro hArc1 hArc2 hCycle
  have e1 : P1 * n_mid - Q1 * n_start - D1 = 0 := by omega
  have e2 : P2 * n_final - Q2 * n_mid - D2 = 0 := by omega
  have e3 : n_final - n_start = 0 := by omega
  have hPosSum : ((P1 * P2 - Q1 * Q2) * (n_start - n_mid)) - ((Q2 - P2) * D1 + (P1 - Q1) * D2) =
                 (Q2 - P2) * (P1 * n_mid - Q1 * n_start - D1) -
                 (Q1 - P1) * (P2 * n_final - Q2 * n_mid - D2) +
                 ((Q1 - P1) * P2) * (n_final - n_start) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  rw [e1, e2, e3] at hPosSum
  simp only [Int.mul_zero, Int.add_zero, Int.sub_zero] at hPosSum
  refine ⟨by omega, ?_, ?_⟩
  · intro hG1 hG2 hD1 hD2
    have hProd1 : (Q2 - P2) * D1 ≥ 1 := by
      have hNonneg : ((Q2 - P2) - 1) * (D1 - 1) ≥ 0 := Int.mul_nonneg (by omega) (by omega)
      have hExp : ((Q2 - P2) - 1) * (D1 - 1) = (Q2 - P2) * D1 - (Q2 - P2) - D1 + 1 := by
        simp only [Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul]; omega
      omega
    have hProd2 : (P1 - Q1) * D2 ≥ 1 := by
      have hNonneg : ((P1 - Q1) - 1) * (D2 - 1) ≥ 0 := Int.mul_nonneg (by omega) (by omega)
      have hExp : ((P1 - Q1) - 1) * (D2 - 1) = (P1 - Q1) * D2 - (P1 - Q1) - D2 + 1 := by
        simp only [Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul]; omega
      omega
    exact ⟨by omega, by omega, by omega⟩
  · intro hCtot hSumPos
    have hProdPos : (P1 * P2 - Q1 * Q2) * (n_start - n_mid) > 0 := by omega
    by_cases hLe : n_start - n_mid ≤ 0
    · have hNonpos : (P1 * P2 - Q1 * Q2) * (n_start - n_mid) ≤ 0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hLe
      omega
    · omega

/-- **Theorem 20 (Universal Planetary Cyclic Drift Shift Law `p_k D_tot^{(k+1)} - q_gear D_tot^{(k)} = P_tot - Q_tot`
and Dual Residual-Drift Tower `p_{k+1} D_2^{(k+1)} - q_gear D_2^{(k)} = P_{rem,k} - Q_{prev}` for Arbitrary Gear Ratio `q_gear ∈ ℤ`)**: -/
theorem thm20_collatz_dual_drift_tower_and_cyclic_shift_law
    (qGear pk pk1 Premk Qprev Bprev D2k D2k1 nk : Int) :
    let Ptot := pk * Premk
    let Qtot := qGear * Qprev
    let Ctot := Ptot - Qtot
    let Dtot_k  := Qprev + pk * D2k
    let Dtot_k1 := Premk + qGear * D2k
    (pk * Dtot_k1 - qGear * Dtot_k = Ctot) ∧
    (Dtot_k1 = Qprev + pk1 * D2k1 → pk1 * D2k1 - qGear * D2k = Premk - Qprev) ∧
    (Ctot * nk = Dtot_k → pk * (D2k - (Qprev - Bprev)) ≥ 0 →
      Ctot * nk ≥ Qprev + pk * (Qprev - Bprev)) := by
  dsimp
  have hShift : pk * (Premk + qGear * D2k) - qGear * (Qprev + pk * D2k) = pk * Premk - qGear * Qprev := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  refine ⟨hShift, by omega, ?_⟩
  intro hCycle hEnv
  have hSub : pk * (D2k - (Qprev - Bprev)) = pk * D2k - pk * (Qprev - Bprev) := by
    simp only [Int.mul_sub]
  omega

/-- **Theorem 21 (Uniqueness of the Planetary Gear Stationary Point `(p_k - q_gear) n* = 1 ⟹ (p_k = q_gear + 1 ∧ n* = 1)`
for Any Gear Ratio `q_gear ∈ ℤ` and Exact Differential Closure Criterion `Q n_start + D_{a,b} = P` for Reaching `n_final = 1`)**: -/
theorem thm21_collatz_planetary_stationary_point_uniqueness_and_reachability_criterion
    (qGear pk nStar P Q n_start n_final Dab : Int) :
    (nStar ≥ 1 → (pk - qGear) * nStar = 1 → pk = qGear + 1 ∧ nStar = 1) ∧
    (P * n_final - Q * n_start = Dab →
      P * (n_final - 1) = (Q * n_start + Dab) - P ∧
      (n_final = 1 → Q * n_start + Dab = P) ∧
      (P ≠ 0 → Q * n_start + Dab = P → n_final = 1)) := by
  refine ⟨?_, ?_⟩
  · intro hN hStat
    have hPos : pk - qGear ≥ 1 := by
      by_cases h : pk - qGear ≤ 0
      · have hMul : (pk - qGear) * nStar ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg h (by omega)
        omega
      · omega
    have hLe : nStar ≤ (pk - qGear) * nStar := by
      have hDiff : (pk - qGear) * nStar - nStar = (pk - qGear - 1) * nStar := by
        simp only [Int.sub_mul, Int.one_mul]
      have hGe0 : (pk - qGear - 1) * nStar ≥ 0 := Int.mul_nonneg (by omega) (by omega)
      omega
    have hN1 : nStar = 1 := by omega
    rw [hN1, Int.mul_one] at hStat
    exact ⟨by omega, hN1⟩
  · intro hEq
    have hDist : P * (n_final - 1) - ((Q * n_start + Dab) - P) =
                 (P * n_final - Q * n_start) - Dab := by
      simp only [Int.mul_sub, Int.mul_one]; omega
    refine ⟨by omega, by intro h1; rw [h1, Int.mul_one] at hEq; omega, ?_⟩
    intro hPne0 hClose
    have hP0 : P * (n_final - 1) = 0 := by omega
    cases Int.mul_eq_zero.mp hP0 with
    | inl hP => exact False.elim (hPne0 hP)
    | inr hN => omega

/-- **Constructive Fermat Well-Founded Descent to the Stationary Point `1` (`0 Classical.choice`)**: -/
theorem collatz_global_convergence_from_local_descent
    (iter : Nat → Nat → Nat)
    (hZero : ∀ n, iter 0 n = n)
    (hAdd  : ∀ k1 k2 n, iter (k1 + k2) n = iter k2 (iter k1 n))
    (hLocalDescent : ∀ n : Nat, n > 1 → ∃ k : Nat, iter k n ≥ 1 ∧ iter k n < n) :
    ∀ n : Nat, n ≥ 1 → ∃ K : Nat, iter K n = 1 := by
  intro n
  refine Nat.strongRecOn n (fun m ih hm => ?_)
  by_cases h1 : m = 1
  · refine ⟨0, ?_⟩; rw [hZero, h1]
  · have hGt1 : m > 1 := by omega
    obtain ⟨k1, hk1Ge1, hk1Lt⟩ := hLocalDescent m hGt1
    obtain ⟨k2, hk2Eq1⟩ := ih (iter k1 m) hk1Lt hk1Ge1
    refine ⟨k1 + k2, ?_⟩; rw [hAdd, hk2Eq1]

/-- **Theorem 22 (Arbitrary-Stage Fermat Infinite-Descent Reduction `(2^a - 3^b) n > D_{a,b} ↔ n_final < n`
and Universal Pillai-Envelope Descent Criterion)**: -/
theorem thm22_collatz_arbitrary_stage_fermat_descent_reduction
    (P Q n n_final Dab Denv : Int)
    (hP : P > 0)
    (hTraj : P * n_final - Q * n = Dab) :
    let C := P - Q
    (P * (n - n_final) = C * n - Dab) ∧
    (C * n > Dab ↔ n_final < n) ∧
    (Dab ≤ Denv → C * n > Denv → C * n > Dab ∧ n_final < n) := by
  dsimp
  have hId : P * (n - n_final) - ((P - Q) * n - Dab) = Dab - (P * n_final - Q * n) := by
    simp only [Int.mul_sub, Int.sub_mul]; omega
  have hEquiv : (P - Q) * n > Dab ↔ n_final < n := by
    constructor
    · intro hGt
      have hPos : P * (n - n_final) > 0 := by omega
      by_cases hLe : n - n_final ≤ 0
      · have hNonpos : P * (n - n_final) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hLe
        omega
      · omega
    · intro hLt
      have hPos : P * (n - n_final) > 0 := Int.mul_pos hP (by omega)
      omega
  refine ⟨by omega, hEquiv, ?_⟩
  intro hEnv hGtEnv
  have hGt : (P - Q) * n > Dab := by omega
  exact ⟨hGt, hEquiv.mp hGt⟩

/-- **Theorem 23 (Universal Dead-End-Free `q_gear`-Adic Prefix Decomposition `D_{a,b} = P_{pen} + q_gear D_{b-1}`
and `2 P_{tot}` 2-Adic Construction Modulus for Any Gear Ratio `q_gear ∈ ℤ`)**: -/
theorem thm23_collatz_dead_end_free_ternary_prefix_closure
    (qGear Ppen plast Qprev Dprev n n_prime Ptot Dab kb kb_prime : Int) :
    let Qtot := qGear * Qprev
    let Dtot := Ppen + qGear * Dprev
    (Dtot - Ppen = qGear * Dprev) ∧
    (Qtot * n + Dtot = Ppen * plast ↔ Ppen * (plast - 1) = qGear * (Qprev * n + Dprev)) ∧
    (Qtot * n + Dab = Ptot * (2 * kb + 1) →
     Qtot * n_prime + Dab = Ptot * (2 * kb_prime + 1) →
      Qtot * n + Dab = (2 * Ptot) * kb + Ptot ∧
      Qtot * (n - n_prime) = (2 * Ptot) * (kb - kb_prime)) := by
  dsimp
  have hId : (qGear * Qprev * n + (Ppen + qGear * Dprev) - Ppen * plast) =
             (qGear * (Qprev * n + Dprev) - Ppen * (plast - 1)) := by
    simp only [Int.mul_add, Int.mul_sub, Int.mul_one, Int.mul_assoc]; omega
  refine ⟨by omega, ⟨fun h => by omega, fun h => by omega⟩, ?_⟩
  intro h1 h2
  have hExpand1 : Ptot * (2 * kb + 1) = (2 * Ptot) * kb + Ptot := by
    simp only [Int.mul_add, Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hExpand2 : Ptot * (2 * kb_prime + 1) = (2 * Ptot) * kb_prime + Ptot := by
    simp only [Int.mul_add, Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hDiff : (qGear * Qprev) * (n - n_prime) - (2 * Ptot) * (kb - kb_prime) =
               ((qGear * Qprev) * n - (2 * Ptot) * kb) - ((qGear * Qprev) * n_prime - (2 * Ptot) * kb_prime) := by
    simp only [Int.mul_sub]; omega
  exact ⟨by omega, by omega⟩

/-- **Theorem 24 (Counter-Rotating Forward-Backward Planetary Gear Splice in `ℤ_{P_1} × ℤ_{Q_2}`,
Bézout Meeting-Point Reconstruction, and Pure-Driven Sikorsky Chord Law)**: -/
theorem thm24_collatz_counter_rotating_forward_backward_splice_and_bezout_lock
    (P1 Q1 D1 P2 Q2 D2 n_start n_mid u v : Int)
    (hFwd : P1 * n_mid = Q1 * n_start + D1)
    (hBwd : Q2 * n_mid = P2 - D2) :
    (Q2 * (Q1 * n_start + D1) = P1 * (P2 - D2) ∧
     (Q1 * Q2) * n_start + (Q2 * D1 + P1 * D2) = P1 * P2) ∧
    (P1 * v - Q2 * u = 1 → n_mid = v * (Q1 * n_start + D1) - u * (P2 - D2)) ∧
    ((Q1 * Q2) * (n_start - n_mid) = (P1 - Q1) * (P2 - D2) - Q2 * D1) := by
  have hSplice1 : Q2 * (Q1 * n_start + D1) = Q2 * (P1 * n_mid) := by rw [hFwd]
  have hSplice2 : P1 * (P2 - D2) = P1 * (Q2 * n_mid) := by rw [hBwd]
  have hComm : Q2 * (P1 * n_mid) = P1 * (Q2 * n_mid) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hSplice : Q2 * (Q1 * n_start + D1) = P1 * (P2 - D2) := by omega
  have hGlobal : (Q1 * Q2) * n_start + (Q2 * D1 + P1 * D2) - P1 * P2 =
                 Q2 * (Q1 * n_start + D1) - P1 * (P2 - D2) := by
    simp only [Int.mul_add, Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hChordId : (Q1 * Q2) * (n_start - n_mid) - ((P1 - Q1) * (Q2 * n_mid) - Q2 * D1) =
                  Q2 * (Q1 * n_start + D1) - Q2 * (P1 * n_mid) := by
    simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  rw [hBwd, ← hSplice1] at hChordId
  refine ⟨⟨hSplice, by omega⟩, ?_, by omega⟩
  intro hBez
  rw [← hFwd, ← hBwd]
  have hBezId : n_mid - (v * (P1 * n_mid) - u * (Q2 * n_mid)) =
                (1 - (P1 * v - Q2 * u)) * n_mid := by
    simp only [Int.mul_sub, Int.sub_mul, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  rw [hBez] at hBezId
  omega

/-- **Theorem 25 (Universal Planetary Gear-Tooth Meshing `q_gear n_0 + c_tooth = p_0 n_1`
and Inductive Step-Peeling Law for Arbitrary Gear Ratio `q_gear ∈ ℤ` and Tooth Offset `c_tooth ∈ ℤ`)**: -/
theorem thm25_collatz_automatic_2adic_3adic_gear_tooth_meshing_and_step_peeling
    (qGear cTooth Qprev p0 Prem Drem n0 n1 kP kD : Int) :
    ((qGear * Qprev) * n0 + (cTooth * Qprev + p0 * Drem) = p0 * Prem ↔
      Qprev * (qGear * n0 + cTooth) = p0 * (Prem - Drem)) ∧
    (Prem = 2 * kP → Drem = 2 * kD + 1 → (Prem - Drem) - 2 * (kP - kD - 1) = 1) ∧
    (p0 ≠ 0 → qGear * n0 + cTooth = p0 * n1 →
      ((qGear * Qprev) * n0 + (cTooth * Qprev + p0 * Drem) = p0 * Prem ↔ Qprev * n1 + Drem = Prem)) := by
  have hId1 : ((qGear * Qprev) * n0 + (cTooth * Qprev + p0 * Drem) - p0 * Prem) =
              (Qprev * (qGear * n0 + cTooth) - p0 * (Prem - Drem)) := by
    simp only [Int.mul_add, Int.mul_sub, Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  refine ⟨⟨fun h => by omega, fun h => by omega⟩, by intro hP hD; omega, ?_⟩
  intro hp0 hStep
  have hId2 : ((qGear * Qprev) * n0 + (cTooth * Qprev + p0 * Drem) - p0 * Prem) =
              (Qprev * (qGear * n0 + cTooth) - p0 * (Prem - Drem)) := hId1
  rw [hStep] at hId2
  have hFactor : Qprev * (p0 * n1) - p0 * (Prem - Drem) =
                 p0 * (Qprev * n1 + Drem - Prem) := by
    simp only [Int.mul_add, Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  constructor
  · intro h
    have hMul0 : p0 * (Qprev * n1 + Drem - Prem) = 0 := by omega
    cases Int.mul_eq_zero.mp hMul0 with
    | inl h0 => exact False.elim (hp0 h0)
    | inr hRem => omega
  · intro h
    have hRem0 : Qprev * n1 + Drem - Prem = 0 := by omega
    rw [hRem0, Int.mul_zero] at hFactor
    omega

/-- **Theorem 26 (Universal Single-Step Planetary Wronskian Excess Identity
`(q_gear n_ref + c_tooth) n_k - p_k n_ref n_{k+1} = c_tooth (n_k - n_ref)` for Any Gear Ratio `q_gear ∈ ℤ`,
Tooth Offset `c_tooth ∈ ℤ`, and Reference Height `n_ref ∈ ℤ`, plus `P_tot`-Free Bernoulli–Euler Drift Bound)**: -/
theorem thm26_collatz_step_wronskian_excess_identity_and_bernoulli_euler_cycle_lock
    (qGear cTooth pk nk nk1 nref Ptot Qtot n0PowPrev n0 nfinal Dab Bpow : Int)
    (hStep : pk * nk1 = qGear * nk + cTooth) :
    ((qGear * nref + cTooth) * nk - pk * nref * nk1 = cTooth * (nk - nref) ∧
     pk * nref * nk1 - (qGear * nref + cTooth) * nk = cTooth * (nref - nk) ∧
     (cTooth = 1 → nk ≥ nref → pk * nref * nk1 ≤ (qGear * nref + 1) * nk) ∧
     (cTooth = 1 → nk ≤ nref → pk * nref * nk1 ≥ (qGear * nref + 1) * nk)) ∧
    (Ptot * nfinal = Qtot * n0 + Dab →
     Ptot * n0PowPrev * nfinal ≤ Bpow →
      n0PowPrev * Dab ≤ Bpow - Qtot * (n0PowPrev * n0) ∧
      Ptot * n0PowPrev * (n0 - nfinal) ≥ Ptot * (n0PowPrev * n0) - Bpow ∧
      (Ptot * n0PowPrev > 0 → Ptot * (n0PowPrev * n0) > Bpow → nfinal < n0)) := by
  have hProd : pk * nref * nk1 = nref * (pk * nk1) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [hStep] at hProd
  have hWronsk : (qGear * nref + cTooth) * nk - nref * (qGear * nk + cTooth) = cTooth * (nk - nref) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hWronsk2 : nref * (qGear * nk + cTooth) - (qGear * nref + cTooth) * nk = cTooth * (nref - nk) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  refine ⟨⟨by omega, by omega, by intro hc _; subst hc; omega, by intro hc _; subst hc; omega⟩, ?_⟩
  intro hTraj hBern
  have hSub : Ptot * n0PowPrev * nfinal = n0PowPrev * (Ptot * nfinal) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [hTraj] at hSub
  have hExpand : n0PowPrev * (Qtot * n0 + Dab) = Qtot * (n0PowPrev * n0) + n0PowPrev * Dab := by
    simp only [Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hDiff : Ptot * n0PowPrev * (n0 - nfinal) =
               Ptot * (n0PowPrev * n0) - Ptot * n0PowPrev * nfinal := by
    simp only [Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  refine ⟨by omega, by omega, ?_⟩
  intro hPos hGt
  have hPosDiff : (Ptot * n0PowPrev) * (n0 - nfinal) > 0 := by omega
  by_cases hLe : n0 - nfinal ≤ 0
  · have hNonpos : (Ptot * n0PowPrev) * (n0 - nfinal) ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hLe
    omega
  · omega

/-- **Theorem 27 (Pure-Binary Balance Over the Stationary Root `n_ref = n* = 1`,
Dual-Drift Conservation Law `D_{a,b} + E_{a,b} = (F_{tot} - Q_{tot}) n_0`, and `F_{a,b}` Non-Descending Ceiling)**: -/
theorem thm27_collatz_pure_binary_stationary_excess_law_and_dual_drift_conservation
    (Ptot Qtot Ftot n0 nb Dab Eab Fab DeltaE : Int)
    (hD : Ptot * nb - Qtot * n0 = Dab)
    (hE : Ftot * n0 - Ptot * nb = Eab) :
    (Dab + Eab = (Ftot - Qtot) * n0 ∧
     Ptot * (n0 - nb) = Eab - (Ftot - Ptot) * n0 ∧
     (Dab > 0 → Eab ≥ 0 → Dab ≤ (Ftot - Qtot) * n0 ∧ Eab < (Ftot - Qtot) * n0)) ∧
    (Eab = (n0 - 1) * Fab + DeltaE →
      Ptot * (n0 - nb) = (Fab - (Ftot - Ptot)) * n0 - Fab + DeltaE ∧
      (Ptot * (n0 - nb) ≤ 0 → DeltaE ≥ 0 → (Fab - (Ftot - Ptot)) * n0 + DeltaE ≤ Fab)) := by
  have hSum : (Ptot * nb - Qtot * n0) + (Ftot * n0 - Ptot * nb) = (Ftot - Qtot) * n0 := by
    simp only [Int.sub_mul]; omega
  have hDesc1 : Ptot * (n0 - nb) - (Ftot * n0 - Ptot * nb - (Ftot - Ptot) * n0) = 0 := by
    simp only [Int.mul_sub, Int.sub_mul]; omega
  refine ⟨⟨by omega, by omega, by intro _ _; exact ⟨by omega, by omega⟩⟩, ?_⟩
  intro hEsplit
  have hId : Ptot * (n0 - nb) - ((Fab - (Ftot - Ptot)) * n0 - Fab + DeltaE) =
             (Ftot * n0 - Ptot * nb) - ((n0 - 1) * Fab + DeltaE) := by
    simp only [Int.mul_sub, Int.sub_mul, Int.one_mul, Int.mul_comm, Int.mul_left_comm]; omega
  exact ⟨by omega, by intro _ _; omega⟩

/-- **Theorem 28 (Universal Centered Coordinate `m_k = (n_k - 1)/2` for Odd Gear `q_gear = 2 q_half + 1`,
Willis Carrier Differential Balance `z_1(\omega_1 - \omega_H) + z_2(\omega_2 - \omega_H) = 0`,
Two-Axle Differential Rotor Duality `S_+ + S_d = P_{tot} - Q_{tot}`, and Core-Reduced Descent)**: -/
theorem thm28_collatz_centered_stationary_coordinate_and_gear_deviation_law
    (qHalf pk phalf mk mk1 Ptot Qtot n0 nb m0 mb Dab Sd Splus Pr0 q0 Splus_red z1 z2 w1 w2 wH : Int) :
    let qGear := 2 * qHalf + 1
    let nk  := 2 * mk + 1
    let nk1 := 2 * mk1 + 1
    -- 0. Willis carrier planetary differential equation: z₁(ω₁ - ω_H) + z₂(ω₂ - ω_H) = z₁ω₁ + z₂ω₂ - (z₁+z₂)ω_H
    (z1 * (w1 - wH) + z2 * (w2 - wH) = (z1 * w1 + z2 * w2) - (z1 + z2) * wH) ∧
    -- 1. Universal centered single-step law around origin m* = 0 for ANY odd gear q_gear = 2 q_half + 1
    -- (vanishing at stationary gear p_half = q_half + 1, i.e. p_k = q_gear + 1):
    (pk = 2 * phalf → pk * nk1 = qGear * nk + 1 →
      pk * mk1 - qGear * mk = (qHalf + 1) - phalf ∧ (phalf = qHalf + 1 → pk * mk1 = qGear * mk)) ∧
    -- 2. Two-axle differential rotor duality S_+ + S_d = P_tot - Q_tot, gap squeeze, and core-reduced descent:
    (n0 = 2 * m0 + 1 → nb = 2 * mb + 1 →
     Ptot * nb - Qtot * n0 = Dab →
     Sd = Qtot * m0 - Ptot * mb →
     Splus = Ptot * (mb + 1) - Qtot * (m0 + 1) →
      (Splus + Sd = Ptot - Qtot ∧ Splus - Sd = Dab ∧ 2 * Sd = Ptot - Qtot - Dab ∧ 2 * Splus = Dab + (Ptot - Qtot)) ∧
      (Ptot > 0 → (mb ≥ 0 → Qtot * m0 - Sd ≥ 0) ∧ (Qtot * m0 - Sd = 0 ↔ mb = 0)) ∧
      (m0 + 1 = Pr0 * q0 → Splus = Pr0 * Splus_red →
        Ptot * (m0 - mb) = Pr0 * ((Ptot - Qtot) * q0 - Splus_red) ∧
        (Ptot > 0 → Pr0 > 0 → (Ptot - Qtot) * q0 > Splus_red → mb < m0 ∧ nb < n0))) := by
  dsimp
  have hWillis : z1 * (w1 - wH) + z2 * (w2 - wH) = (z1 * w1 + z2 * w2) - (z1 + z2) * wH := by
    simp only [Int.mul_sub, Int.add_mul]; omega
  have hStepCentered : (2 * phalf) * (2 * mk1 + 1) - ((2 * qHalf + 1) * (2 * mk + 1) + 1) =
                       2 * ((2 * phalf) * mk1 - (2 * qHalf + 1) * mk - ((qHalf + 1) - phalf)) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  refine ⟨hWillis, ?_, ?_⟩
  · intro hpk hStep
    rw [hpk] at hStep ⊢
    exact ⟨by omega, by intro _; omega⟩
  · intro hn0 hnb hTraj hSd hSplus
    have hSum : (Ptot * (mb + 1) - Qtot * (m0 + 1)) + (Qtot * m0 - Ptot * mb) = Ptot - Qtot := by
      simp only [Int.mul_add, Int.mul_one]; omega
    have h2m0 : 2 * m0 + 1 = m0 + m0 + 1 := by omega
    have h2mb : 2 * mb + 1 = mb + mb + 1 := by omega
    have hDiff : (Ptot * (mb + 1) - Qtot * (m0 + 1)) - (Qtot * m0 - Ptot * mb) =
                 Ptot * (mb + mb + 1) - Qtot * (m0 + m0 + 1) := by
      simp only [Int.mul_add, Int.mul_one]; omega
    rw [← h2m0, ← h2mb, ← hn0, ← hnb, hTraj] at hDiff
    have hDesc : Ptot * (m0 - mb) - ((Ptot - Qtot) * (m0 + 1) - (Ptot * (mb + 1) - Qtot * (m0 + 1))) = 0 := by
      simp only [Int.mul_sub, Int.sub_mul, Int.mul_add, Int.mul_one]; omega
    refine ⟨⟨by omega, by omega, by omega, by omega⟩, ?_, ?_⟩
    · intro hPpos
      have hGap : Qtot * m0 - Sd = Ptot * mb := by omega
      refine ⟨by intro hmb; have := Int.mul_nonneg (by omega : Ptot ≥ 0) hmb; omega, ?_⟩
      constructor
      · intro hZero
        have hMul0 : Ptot * mb = 0 := by omega
        cases Int.mul_eq_zero.mp hMul0 with
        | inl hP0 => omega
        | inr hmb0 => exact hmb0
      · intro hmb0; rw [hmb0, Int.mul_zero] at hGap; exact hGap
    · intro hm0Core hSplusCore
      have hRed : (Ptot - Qtot) * (Pr0 * q0) - Pr0 * Splus_red =
                  Pr0 * ((Ptot - Qtot) * q0 - Splus_red) := by
        simp only [Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      rw [← hm0Core, ← hSplusCore] at hRed
      have hMainRed : Ptot * (m0 - mb) = Pr0 * ((Ptot - Qtot) * q0 - Splus_red) := by omega
      refine ⟨hMainRed, ?_⟩
      intro hPpos hPr0pos hGt
      have hRhsPos : Pr0 * ((Ptot - Qtot) * q0 - Splus_red) > 0 := Int.mul_pos hPr0pos (by omega)
      have hMbLt : mb < m0 := by
        by_cases hLe : m0 - mb ≤ 0
        · have hNonpos : Ptot * (m0 - mb) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hLe
          omega
        · omega
      exact ⟨hMbLt, by omega⟩

/-- **Theorem 29 (Unified Macro-Step & Odd-Core Dynamics: Double `SL₂(ℤ)` Bézout Lock, Core-Free Macro Gap Jump,
Unconditional Core Descent `q_1 < q_0` at `r_0 = 0`, and Two-Macro-Step Tail Compensation)**: -/
theorem thm29_collatz_trailing_ones_burn_macro_step
    (Pr0 Pr1 Qr1 Pr1_next pbeta0 pbeta1 Pr2 Qr2 q0 q1 q2 n0 n1 m0 m1 : Int)
    (hn0  : n0 + 1 = Pr1 * q0)
    (hMac : pbeta0 * n1 + 1 = Qr1 * q0)
    (hn1  : n1 + 1 = Pr1_next * q1) :
    -- 1. Minimal-drift macro-step law, double SL₂(ℤ) Bézout lock (= +1), and homogeneous core difference:
    ((Pr1 * pbeta0) * n1 - Qr1 * n0 = Qr1 - Pr1 ∧
     Pr1 * q0 - n0 = 1 ∧
     Qr1 * q0 - pbeta0 * n1 = 1 ∧
     pbeta0 * n1 - n0 = (Qr1 - Pr1) * q0) ∧
    -- 2. Core-free macro-step gap jump (q_0 cancels identically!):
    (m0 = Pr0 * q0 - 1 → n1 = 2 * m1 + 1 →
      Qr1 * m0 - (2 * Pr0 * pbeta0) * m1 = Pr0 * (pbeta0 + 1) - Qr1) ∧
    -- 3. Odd-core transition law q_0 -> q_1 and unconditional strict descent q_1 < q_0 at r_0 = 0 (Q_r1 = 3):
    ((pbeta0 * Pr1_next) * q1 - Qr1 * q0 = pbeta0 - 1 ∧
     (Qr1 = 3 →
       (pbeta0 * Pr1_next) * (q0 - q1) =
         pbeta0 * (Pr1_next - 2) * q0 + (pbeta0 - 2) * (2 * q0 - 1) + (q0 - 1) ∧
       (pbeta0 ≥ 2 → Pr1_next ≥ 2 → q0 ≥ 2 → q1 < q0))) ∧
    -- 4. Two-macro-step odd-core tail compensation q_0 -> q_1 -> q_2:
    ((pbeta1 * Pr2) * q2 - Qr2 * q1 = pbeta1 - 1 →
      let Pcomp := (pbeta0 * Pr1_next) * (pbeta1 * Pr2)
      let Qcomp := Qr1 * Qr2
      let Dcomp := Qr2 * (pbeta0 - 1) + (pbeta0 * Pr1_next) * (pbeta1 - 1)
      Pcomp * q2 - Qcomp * q0 = Dcomp ∧ Pcomp * (q0 - q2) = (Pcomp - Qcomp) * q0 - Dcomp) := by
  have h1 : (Pr1 * pbeta0) * n1 + Pr1 = Pr1 * (pbeta0 * n1 + 1) := by
    simp only [Int.mul_add, Int.mul_one, Int.mul_assoc]
  rw [hMac] at h1
  have h2 : Qr1 * n0 + Qr1 = Qr1 * (n0 + 1) := by
    simp only [Int.mul_add, Int.mul_one]
  rw [hn0] at h2
  have hComm12 : Pr1 * (Qr1 * q0) = Qr1 * (Pr1 * q0) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hHomog : (pbeta0 * n1 - n0) - (Qr1 - Pr1) * q0 =
               (pbeta0 * n1 + 1 - Qr1 * q0) - (n0 + 1 - Pr1 * q0) := by
    simp only [Int.sub_mul]; omega
  have hCore1 : (pbeta0 * Pr1_next) * q1 = pbeta0 * (Pr1_next * q1) := by
    simp only [Int.mul_assoc]
  rw [← hn1] at hCore1
  have hCore2 : pbeta0 * (n1 + 1) = (pbeta0 * n1 + 1) + (pbeta0 - 1) := by
    simp only [Int.mul_add, Int.mul_one]; omega
  rw [hMac] at hCore2
  have hCoreLaw : (pbeta0 * Pr1_next) * q1 - Qr1 * q0 = pbeta0 - 1 := by omega
  refine ⟨⟨by omega, by omega, by omega, by omega⟩, ?_, ⟨hCoreLaw, ?_⟩, ?_⟩
  · intro hm0 hn1m1
    have hCancel : (Qr1 * (Pr0 * q0 - 1) - (2 * Pr0 * pbeta0) * m1) - (Pr0 * (pbeta0 + 1) - Qr1) =
                   Pr0 * ((Qr1 * q0) - (pbeta0 * (2 * m1 + 1) + 1)) := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
    rw [← hm0, ← hn1m1, hMac, Int.sub_self, Int.mul_zero] at hCancel
    omega
  · intro hQr3
    rw [hQr3] at hCoreLaw
    have hDecompId : ((pbeta0 * Pr1_next) * q0 - (3 * q0 + (pbeta0 - 1))) -
                     (pbeta0 * (Pr1_next - 2) * q0 + (pbeta0 - 2) * (2 * q0 - 1) + (q0 - 1)) = 0 := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
    have hDiffExpand : (pbeta0 * Pr1_next) * (q0 - q1) = (pbeta0 * Pr1_next) * q0 - (pbeta0 * Pr1_next) * q1 := by
      simp only [Int.mul_sub]
    refine ⟨by omega, ?_⟩
    intro hpbeta hPrnext hq0
    have hTerm1 : pbeta0 * (Pr1_next - 2) * q0 ≥ 0 :=
      Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)
    have hTerm2 : (pbeta0 - 2) * (2 * q0 - 1) ≥ 0 :=
      Int.mul_nonneg (by omega) (by omega)
    have hPosProd : pbeta0 * Pr1_next > 0 := Int.mul_pos (by omega) (by omega)
    by_cases hLe : q0 - q1 ≤ 0
    · have hNonpos : (pbeta0 * Pr1_next) * (q0 - q1) ≤ 0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hLe
      omega
    · omega
  · intro hStep1
    dsimp
    have hElim : ((pbeta0 * Pr1_next) * (pbeta1 * Pr2) * q2 - (Qr1 * Qr2) * q0) -
                 (Qr2 * (pbeta0 - 1) + (pbeta0 * Pr1_next) * (pbeta1 - 1)) =
                 (pbeta0 * Pr1_next) * ((pbeta1 * Pr2) * q2 - Qr2 * q1 - (pbeta1 - 1)) +
                 Qr2 * ((pbeta0 * Pr1_next) * q1 - Qr1 * q0 - (pbeta0 - 1)) := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
    have e0 : (pbeta0 * Pr1_next) * q1 - Qr1 * q0 - (pbeta0 - 1) = 0 := by omega
    have e1 : (pbeta1 * Pr2) * q2 - Qr2 * q1 - (pbeta1 - 1) = 0 := by omega
    rw [e0, e1] at hElim
    simp only [Int.mul_zero, Int.add_zero] at hElim
    have hComp2 : (pbeta0 * Pr1_next) * (pbeta1 * Pr2) * (q0 - q2) =
                  (pbeta0 * Pr1_next) * (pbeta1 * Pr2) * q0 - (pbeta0 * Pr1_next) * (pbeta1 * Pr2) * q2 := by
      simp only [Int.mul_sub]
    have hComp3 : ((pbeta0 * Pr1_next) * (pbeta1 * Pr2) - Qr1 * Qr2) * q0 =
                  (pbeta0 * Pr1_next) * (pbeta1 * Pr2) * q0 - (Qr1 * Qr2) * q0 := by
      simp only [Int.sub_mul]
    exact ⟨by omega, by omega⟩

#print axioms thm18_universal_arbitrary_modulus_rotator_and_two_arc_trajectory_wronskian
#print axioms thm19_collatz_catalan_sl2_basis_drift_bounds_and_positive_wronskian_sum
#print axioms thm20_collatz_dual_drift_tower_and_cyclic_shift_law
#print axioms thm21_collatz_planetary_stationary_point_uniqueness_and_reachability_criterion
#print axioms collatz_global_convergence_from_local_descent
#print axioms thm22_collatz_arbitrary_stage_fermat_descent_reduction
#print axioms thm23_collatz_dead_end_free_ternary_prefix_closure
#print axioms thm24_collatz_counter_rotating_forward_backward_splice_and_bezout_lock
#print axioms thm25_collatz_automatic_2adic_3adic_gear_tooth_meshing_and_step_peeling
#print axioms thm26_collatz_step_wronskian_excess_identity_and_bernoulli_euler_cycle_lock
#print axioms thm27_collatz_pure_binary_stationary_excess_law_and_dual_drift_conservation
#print axioms thm28_collatz_centered_stationary_coordinate_and_gear_deviation_law
#print axioms thm29_collatz_trailing_ones_burn_macro_step

end RotatorCalculusPaper
