import AxiomGuard

namespace RotatorCalculusPaper

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000

/-- **Theorem 18 (Two-Arc Pillai–Wronskian Trajectory Composition & Cycle Chord Law, `0 Prop premises`)**: -/
theorem thm18_arbitrary_modulus_rotator_and_two_arc_trajectory_wronskian
    (P1 Q1 P2 Q2 n_start n_mid n_final : Int) :
    let D1 := P1 * n_mid - Q1 * n_start
    let D2 := P2 * n_final - Q2 * n_mid
    let C1 := P1 - Q1
    let C2 := P2 - Q2
    let Ctot := P1 * P2 - Q1 * Q2
    let Dtot := Q2 * D1 + P1 * D2
    ((P1 * P2) * n_final - (Q1 * Q2) * n_start = Dtot) ∧
    (Ctot = Q2 * C1 + P1 * C2 ∧ Ctot = P2 * C1 + Q1 * C2) ∧
    ((P1 * P2) * (n_final - n_start) + Ctot * n_start = Dtot) ∧
    (n_final = n_start →
      (Ctot * n_start = Q2 * D1 + P1 * D2) ∧
      (Ctot * n_mid   = P2 * D1 + Q1 * D2) ∧
      (Ctot * (n_mid - n_start) = C2 * D1 - C1 * D2)) := by
  dsimp
  have hComp : ((P1 * P2) * n_final - (Q1 * Q2) * n_start) -
               (Q2 * (P1 * n_mid - Q1 * n_start) + P1 * (P2 * n_final - Q2 * n_mid)) = 0 := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hDisp1 : ((P1 * P2) * (n_final - n_start) + (P1 * P2 - Q1 * Q2) * n_start) -
                ((P1 * P2) * n_final - (Q1 * Q2) * n_start) = 0 := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hCycMid : ((P1 * P2 - Q1 * Q2) * n_mid) -
                 (P2 * (P1 * n_mid - Q1 * n_start) + Q1 * (P2 * n_final - Q2 * n_mid)) =
                 (Q1 * P2) * (n_start - n_final) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hWronsk : ((P1 * P2 - Q1 * Q2) * (n_mid - n_start)) -
                 ((P2 - Q2) * (P1 * n_mid - Q1 * n_start) - (P1 - Q1) * (P2 * n_final - Q2 * n_mid)) =
                 ((Q1 - P1) * P2) * (n_start - n_final) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  refine ⟨by omega,
          ⟨by simp only [Int.mul_sub, Int.sub_mul, Int.mul_comm, Int.mul_left_comm]; omega,
           by simp only [Int.mul_sub, Int.sub_mul, Int.mul_comm, Int.mul_left_comm]; omega⟩,
          by omega, ?_⟩
  intro hCycle
  have e3 : n_start - n_final = 0 := by omega
  have e4 : n_final - n_start = 0 := by omega
  rw [e4] at hDisp1
  rw [e3] at hCycMid hWronsk
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
    (2 * 2 - 3 * 1 = 1 ∧ 2 * u + 3 * v = a ∧ u + 2 * v = b ∧ u + v = a - b) ∧
    (Ctot = P2 * G1 - Q1 * G2 ∧ Ctot = Q2 * G1 - P1 * G2) ∧
    (P1 * n_mid - Q1 * n_start = D1 → P2 * n_final - Q2 * n_mid = D2 → n_final = n_start →
      (Ctot * (n_start - n_mid) = G2 * D1 + G1 * D2) ∧
      (Ctot > 0 → G2 * D1 + G1 * D2 > 0 → n_start > n_mid)) := by
  dsimp
  refine ⟨⟨by omega, by omega, by omega, by omega⟩,
          ⟨by simp only [Int.mul_sub, Int.sub_mul, Int.mul_comm, Int.mul_left_comm]; omega,
           by simp only [Int.mul_sub, Int.sub_mul, Int.mul_comm, Int.mul_left_comm]; omega⟩, ?_⟩
  intro hArc1 hArc2 hCycle
  have hPosSum : ((P1 * P2 - Q1 * Q2) * (n_start - n_mid)) - ((Q2 - P2) * D1 + (P1 - Q1) * D2) =
                 (Q2 - P2) * (P1 * n_mid - Q1 * n_start - D1) -
                 (Q1 - P1) * (P2 * n_final - Q2 * n_mid - D2) +
                 ((Q1 - P1) * P2) * (n_final - n_start) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have e1 : P1 * n_mid - Q1 * n_start - D1 = 0 := by omega
  have e2 : P2 * n_final - Q2 * n_mid - D2 = 0 := by omega
  have e3 : n_final - n_start = 0 := by omega
  rw [e1, e2, e3] at hPosSum
  refine ⟨by omega, ?_⟩
  intro hCtot hSumPos
  by_cases hLe : n_start - n_mid ≤ 0
  · have := Int.mul_nonpos_of_nonneg_of_nonpos (by omega : P1 * P2 - Q1 * Q2 ≥ 0) hLe; omega
  · omega

/-- **Theorem 20 (Planetary Cyclic Drift Shift Law `p_k D_tot^{(k+1)} - q_gear D_tot^{(k)} = P_tot - Q_tot`)**: -/
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
  refine ⟨by simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega,
          by omega, ?_⟩
  intro _ _; have : pk * (D2k - (Qprev - Bprev)) = pk * D2k - pk * (Qprev - Bprev) := by simp only [Int.mul_sub]
  omega

/-- **Theorem 21 (Uniqueness of the Planetary Gear Stationary Point `(p_k - q_gear) n* = 1 ⟹ (p_k = q_gear + 1 ∧ n* = 1)`
and Exact Differential Closure Criterion `Q n_start + D_{a,b} = P` for Reaching `n_final = 1`)**: -/
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
      · have := Int.mul_nonpos_of_nonpos_of_nonneg h (by omega : nStar ≥ 0); omega
      · omega
    have hDiff : (pk - qGear) * nStar - nStar = (pk - qGear - 1) * nStar := by simp only [Int.sub_mul, Int.one_mul]
    have hGe0 : (pk - qGear - 1) * nStar ≥ 0 := Int.mul_nonneg (by omega) (by omega)
    have hN1 : nStar = 1 := by omega
    rw [hN1, Int.mul_one] at hStat; exact ⟨by omega, hN1⟩
  · intro hEq
    have hDist : P * (n_final - 1) - ((Q * n_start + Dab) - P) = (P * n_final - Q * n_start) - Dab := by
      simp only [Int.mul_sub, Int.mul_one]; omega
    refine ⟨by omega, by intro h1; rw [h1, Int.mul_one] at hEq; omega, ?_⟩
    intro hPne0 hClose
    cases Int.mul_eq_zero.mp (by omega : P * (n_final - 1) = 0) with
    | inl hP => exact False.elim (hPne0 hP)
    | inr hN => omega

/-- **Theorem 22 (Arbitrary-Stage Fermat Infinite-Descent Reduction `(P - Q) n > D_{a,b} ↔ n_final < n`,
Symmetric Group `S_b` Adjacent-Transposition Monotonicity, and the Two-Policemen Permutation Squeeze, `0 non-order Prop premises`)**: -/
theorem thm22_collatz_arbitrary_stage_fermat_descent_reduction
    (P Q Pb Pab wk pk pk1 Drest n n_final : Int)
    (hP : P > 0) :
    let Dab := P * n_final - Q * n
    let C := P - Q
    let Dorig := Drest + wk * pk
    let Dswap := Drest + wk * pk1
    let Dmin  := Q - Pb
    let Dmax  := Pab * (Q - Pb)
    (P * (n - n_final) = C * n - Dab ∧ (C * n > Dab ↔ n_final < n)) ∧
    (Dswap - Dorig = wk * (pk1 - pk) ∧ (wk > 0 → (pk < pk1 ↔ Dorig < Dswap))) ∧
    (P = Pab * Pb → Dmin ≤ Dab → Dab ≤ Dmax →
      Q * (n + 1) - Pb ≤ P * n_final ∧
      P * n_final ≤ Q * (n + Pab) - P ∧
      P * (n - n_final) ≥ P * (n + 1) - Q * (n + Pab)) ∧
    (C > 0 → n_final = n → P - Q ≤ Dab → Dab ≤ P - Q → n = 1) := by
  dsimp
  have hId : P * (n - n_final) - ((P - Q) * n - (P * n_final - Q * n)) = 0 := by
    simp only [Int.mul_sub, Int.sub_mul]; omega
  have hEquiv : (P - Q) * n > P * n_final - Q * n ↔ n_final < n := by
    constructor
    · intro hGt
      by_cases hLe : n - n_final ≤ 0
      · have := Int.mul_nonpos_of_nonneg_of_nonpos (by omega : P ≥ 0) hLe; omega
      · omega
    · intro hLt; have := Int.mul_pos hP (by omega : n - n_final > 0); omega
  refine ⟨⟨by omega, hEquiv⟩, ⟨by simp only [Int.mul_sub]; omega, ?_⟩, ?_, ?_⟩
  · intro hWkPos
    have hSwapId : (Drest + wk * pk1) - (Drest + wk * pk) = wk * (pk1 - pk) := by simp only [Int.mul_sub]; omega
    constructor
    · intro hLt; have := Int.mul_pos hWkPos (by omega : pk1 - pk > 0); omega
    · intro hDLt
      by_cases hLe : pk1 - pk ≤ 0
      · have := Int.mul_nonpos_of_nonneg_of_nonpos (by omega : wk ≥ 0) hLe; omega
      · omega
  · intro hPprod hDmin hDmax
    have hL : (P * n_final) - (Q * (n + 1) - Pb) = (P * n_final - Q * n) - (Q - Pb) := by
      simp only [Int.mul_add, Int.mul_one]; omega
    have hR : (Q * (n + Pab) - P) - (P * n_final) =
              (Pab * (Q - Pb) - (P * n_final - Q * n)) + (Pab * Pb - P) + (Q * Pab - Pab * Q) := by
      simp only [Int.mul_add, Int.mul_sub]; omega
    have hCommQP : Q * Pab = Pab * Q := Int.mul_comm Q Pab
    have hDescSq : P * (n - n_final) - (P * (n + 1) - Q * (n + Pab)) = (Q * (n + Pab) - P) - (P * n_final) := by
      simp only [Int.mul_sub, Int.mul_add, Int.mul_one]; omega
    exact ⟨by omega, by omega, by omega⟩
  · intro hCpos hCyc hGe hLe
    have hCyc1 : (P - Q) * (n - 1) = (P * n_final - Q * n) - (P - Q) - P * (n_final - n) := by
      simp only [Int.mul_sub, Int.sub_mul, Int.mul_one]; omega
    have hSub0 : n_final - n = 0 := by omega
    rw [hSub0, Int.mul_zero] at hCyc1
    cases Int.mul_eq_zero.mp (by omega : (P - Q) * (n - 1) = 0) with
    | inl hC0 => omega
    | inr hn1 => omega

/-- **Theorem 23 (Dead-End-Free `q_gear`-Adic Prefix Decomposition `D_{a,b} = P_{pen} + q_gear D_{b-1}`
and `2 P_{tot}` 2-Adic Construction Modulus)**: -/
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
  refine ⟨by omega, ⟨fun _ => by omega, fun _ => by omega⟩, ?_⟩
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
Bézout Meeting-Point Reconstruction, and Pure-Driven Sikorsky Chord Law, `0 Prop premises`)**: -/
theorem thm24_collatz_counter_rotating_forward_backward_splice_and_bezout_lock
    (P1 Q1 P2 Q2 n_start n_mid u v : Int) :
    let D1 := P1 * n_mid - Q1 * n_start
    let D2 := P2 - Q2 * n_mid
    let dBez := P1 * v - Q2 * u
    (Q2 * (Q1 * n_start + D1) = P1 * (P2 - D2) ∧
     (Q1 * Q2) * n_start + (Q2 * D1 + P1 * D2) = P1 * P2) ∧
    (dBez * n_mid = v * (Q1 * n_start + D1) - u * (P2 - D2)) ∧
    ((Q1 * Q2) * (n_start - n_mid) = (P1 - Q1) * (P2 - D2) - Q2 * D1) := by
  dsimp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)

/-- **Theorem 25 (Planetary Gear-Tooth Meshing `q_gear n_0 + c_tooth = p_0 n_1`
and Inductive Step-Peeling Law)**: -/
theorem thm25_collatz_automatic_2adic_3adic_gear_tooth_meshing_and_step_peeling
    (qGear cTooth Qprev p0 Prem Drem n0 n1 : Int) :
    ((qGear * Qprev) * n0 + (cTooth * Qprev + p0 * Drem) = p0 * Prem ↔
      Qprev * (qGear * n0 + cTooth) = p0 * (Prem - Drem)) ∧
    (p0 ≠ 0 → qGear * n0 + cTooth = p0 * n1 →
      ((qGear * Qprev) * n0 + (cTooth * Qprev + p0 * Drem) = p0 * Prem ↔ Qprev * n1 + Drem = Prem)) := by
  have hId1 : ((qGear * Qprev) * n0 + (cTooth * Qprev + p0 * Drem) - p0 * Prem) =
              (Qprev * (qGear * n0 + cTooth) - p0 * (Prem - Drem)) := by
    simp only [Int.mul_add, Int.mul_sub, Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  refine ⟨⟨fun _ => by omega, fun _ => by omega⟩, ?_⟩
  intro hp0 hStep
  have hId2 := hId1; rw [hStep] at hId2
  have hFactor : Qprev * (p0 * n1) - p0 * (Prem - Drem) = p0 * (Qprev * n1 + Drem - Prem) := by
    simp only [Int.mul_add, Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  constructor
  · intro _
    cases Int.mul_eq_zero.mp (by omega : p0 * (Qprev * n1 + Drem - Prem) = 0) with
    | inl h0 => exact False.elim (hp0 h0)
    | inr hRem => omega
  · intro h
    have hRem0 : Qprev * n1 + Drem - Prem = 0 := by omega
    rw [hRem0, Int.mul_zero] at hFactor; omega

/-- **Theorem 26 (Single-Step Planetary Wronskian Excess Identity
`(q_gear n_ref + c_tooth) n_k - p_k n_ref n_{k+1} = c_tooth (n_k - n_ref)` and Bernoulli–Euler Drift Bound, `0 Prop premises`)**: -/
theorem thm26_collatz_step_wronskian_excess_identity_and_bernoulli_euler_cycle_lock
    (qGear pk nk nk1 nref Ptot Qtot n0PowPrev n0 nfinal Dab Bpow : Int) :
    let cTooth := pk * nk1 - qGear * nk
    ((qGear * nref + cTooth) * nk - pk * nref * nk1 = cTooth * (nk - nref)) ∧
    (Ptot * nfinal = Qtot * n0 + Dab →
     Ptot * n0PowPrev * nfinal ≤ Bpow →
      n0PowPrev * Dab ≤ Bpow - Qtot * (n0PowPrev * n0) ∧
      Ptot * n0PowPrev * (n0 - nfinal) ≥ Ptot * (n0PowPrev * n0) - Bpow) := by
  dsimp
  have hWronsk : (qGear * nref + (pk * nk1 - qGear * nk)) * nk - pk * nref * nk1 =
                 (pk * nk1 - qGear * nk) * (nk - nref) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  refine ⟨hWronsk, ?_⟩
  intro hTraj hBern
  have hSub : Ptot * n0PowPrev * nfinal = n0PowPrev * (Ptot * nfinal) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [hTraj] at hSub
  have hExpand : n0PowPrev * (Qtot * n0 + Dab) = Qtot * (n0PowPrev * n0) + n0PowPrev * Dab := by
    simp only [Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hDiff : Ptot * n0PowPrev * (n0 - nfinal) = Ptot * (n0PowPrev * n0) - Ptot * n0PowPrev * nfinal := by
    simp only [Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  exact ⟨by omega, by omega⟩

/-- **Theorem 27 (Pure-Binary Balance Over the Stationary Root `n_ref = n* = 1`,
Dual-Drift Conservation Law `D_{a,b} + E_{a,b} = (F_{tot} - Q_{tot}) n_0`, and Upper-Ceiling Screw `(U_d, U_+)`, `0 Prop premises`)**: -/
theorem thm27_collatz_pure_binary_stationary_excess_law_and_dual_drift_conservation
    (Ptot Qtot Ftot m0 mb : Int) :
    let n0    := m0 + m0 + 1
    let nb    := mb + mb + 1
    let Dab   := Ptot * nb - Qtot * n0
    let Eab   := Ftot * n0 - Ptot * nb
    let Ud    := Ftot * m0 - Ptot * mb
    let Uplus := Ptot * (mb + 1) - Ftot * (m0 + 1)
    let Splus := Ptot * (mb + 1) - Qtot * (m0 + 1)
    (Dab + Eab = (Ftot - Qtot) * n0 ∧ Ptot * (n0 - nb) = Eab - (Ftot - Ptot) * n0) ∧
    (Ud + Uplus = Ptot - Ftot ∧
     Ud - Uplus = Eab ∧
     Splus + Ud = (Ftot - Qtot) * m0 + (Ptot - Qtot)) := by
  dsimp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
                Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)

/-- **Theorem 28 (Willis Carrier Differential Balance `z_1(ω_1 - ω_H) + z_2(ω_2 - ω_H) = 0`,
Centered Coordinate `m_k = (n_k - 1)/2`, and Two-Axle Differential Rotor Duality `S_+ + S_d = P_{tot} - Q_{tot}`)**: -/
theorem thm28_collatz_centered_stationary_coordinate_and_gear_deviation_law
    (qHalf pk phalf mk mk1 Ptot Qtot n0 nb m0 mb Dab Sd Splus Pr0 q0 Splus_red z1 z2 w1 w2 wH : Int) :
    let qGear := 2 * qHalf + 1
    let nk  := 2 * mk + 1
    let nk1 := 2 * mk1 + 1
    (z1 * (w1 - wH) + z2 * (w2 - wH) = (z1 * w1 + z2 * w2) - (z1 + z2) * wH) ∧
    (pk = 2 * phalf → pk * nk1 = qGear * nk + 1 →
      pk * mk1 - qGear * mk = (qHalf + 1) - phalf) ∧
    (n0 = 2 * m0 + 1 → nb = 2 * mb + 1 →
     Ptot * nb - Qtot * n0 = Dab →
     Sd = Qtot * m0 - Ptot * mb →
     Splus = Ptot * (mb + 1) - Qtot * (m0 + 1) →
      (Splus + Sd = Ptot - Qtot ∧ Splus - Sd = Dab ∧ Qtot * m0 - Sd = Ptot * mb) ∧
      (m0 + 1 = Pr0 * q0 → Splus = Pr0 * Splus_red →
        Ptot * (m0 - mb) = Pr0 * ((Ptot - Qtot) * q0 - Splus_red))) := by
  dsimp
  have hWillis : z1 * (w1 - wH) + z2 * (w2 - wH) = (z1 * w1 + z2 * w2) - (z1 + z2) * wH := by
    simp only [Int.mul_sub, Int.add_mul]; omega
  have hStepCentered : (2 * phalf) * (2 * mk1 + 1) - ((2 * qHalf + 1) * (2 * mk + 1) + 1) =
                       2 * ((2 * phalf) * mk1 - (2 * qHalf + 1) * mk - ((qHalf + 1) - phalf)) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  refine ⟨hWillis, by intro hpk _; rw [hpk] at *; omega, ?_⟩
  intro hn0 hnb hTraj hSd hSplus
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
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  intro hm0Core hSplusCore
  have hRed : (Ptot - Qtot) * (Pr0 * q0) - Pr0 * Splus_red = Pr0 * ((Ptot - Qtot) * q0 - Splus_red) := by
    simp only [Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [← hm0Core, ← hSplusCore] at hRed
  omega

/-- Cumulative binary exponent `A_M = ∑_{m=0}^{M-1} (β_m + r_{m+1} + 1)` across `M` macro-steps. -/
def macroSumA : List (Int × Int) → Int
  | [] => 0
  | (beta, rNext) :: rest => (beta + rNext + 1) + macroSumA rest

/-- Cumulative ternary exponent `B_M = ∑_{m=0}^{M-1} (r_m + 1)` starting from `r_0`. -/
def macroSumB : Int → List (Int × Int) → Int
  | _, [] => 0
  | rCurr, (_, rNext) :: rest => (rCurr + 1) + macroSumB rNext rest

/-- Total even-reset exponent sum `∑_{m=0}^{M-1} β_m` across `M` macro-steps. -/
def macroSumBeta : List (Int × Int) → Int
  | [] => 0
  | (beta, _) :: rest => beta + macroSumBeta rest

/-- Final trailing-ones count `r_M` after `M` macro-steps starting from `r_0`. -/
def macroFinalR : Int → List (Int × Int) → Int
  | rCurr, [] => rCurr
  | _, (_, rNext) :: rest => macroFinalR rNext rest

/-- Cumulative Catalan descent drift `∑_{m=0}^{M-1} (2 β_m - 1 - r_m)` across `M` macro-steps. -/
def macroCatalanDrift : Int → List (Int × Int) → Int
  | _, [] => 0
  | rCurr, (beta, rNext) :: rest => (2 * beta - 1 - rCurr) + macroCatalanDrift rNext rest

/-- Total binary gear pitch `P_tot(L) = ∏_{(P, Q, D) ∈ L} P` of an arbitrary `M`-screw cascade `L`. -/
def multiScrewP : List (Int × Int × Int) → Int
  | [] => 1
  | (p, _, _) :: rest => p * multiScrewP rest

/-- Total ternary gear pitch `Q_tot(L) = ∏_{(P, Q, D) ∈ L} Q` of an arbitrary `M`-screw cascade `L`. -/
def multiScrewQ : List (Int × Int × Int) → Int
  | [] => 1
  | (_, q, _) :: rest => q * multiScrewQ rest

/-- Composite gap modulus `C_tot(L) = P_tot(L) - Q_tot(L)` of an arbitrary `M`-screw cascade `L`. -/
def multiScrewC (screws : List (Int × Int × Int)) : Int :=
  multiScrewP screws - multiScrewQ screws

/-- Composite planetary drift accumulator `D_tot(L)` of an arbitrary `M`-screw cascade `L`. -/
def multiScrewD : List (Int × Int × Int) → Int
  | [] => 0
  | (p, _, d) :: rest => multiScrewQ rest * d + p * multiScrewD rest

theorem multiScrewP_append (L1 L2 : List (Int × Int × Int)) :
    multiScrewP (L1 ++ L2) = multiScrewP L1 * multiScrewP L2 := by
  induction L1 with
  | nil => dsimp [multiScrewP]; omega
  | cons hd tl ih => rcases hd with ⟨p, q, d⟩; dsimp [multiScrewP]; rw [ih]; simp only [Int.mul_assoc]

theorem multiScrewQ_append (L1 L2 : List (Int × Int × Int)) :
    multiScrewQ (L1 ++ L2) = multiScrewQ L1 * multiScrewQ L2 := by
  induction L1 with
  | nil => dsimp [multiScrewQ]; omega
  | cons hd tl ih => rcases hd with ⟨p, q, d⟩; dsimp [multiScrewQ]; rw [ih]; simp only [Int.mul_assoc]

theorem multiScrewD_append (L1 L2 : List (Int × Int × Int)) :
    multiScrewD (L1 ++ L2) = multiScrewQ L2 * multiScrewD L1 + multiScrewP L1 * multiScrewD L2 := by
  induction L1 with
  | nil => dsimp [multiScrewD, multiScrewP]; simp only [Int.mul_zero, Int.zero_add, Int.one_mul]
  | cons hd tl ih =>
    rcases hd with ⟨p, q, d⟩; dsimp [multiScrewD, multiScrewP]; rw [multiScrewQ_append, ih]
    simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega

/-- **Theorem 29 (Unified Multi-Screw Planetary Cascade Monoid, Double `SL₂(ℤ)` Bézout Lock,
Exclusion of the `2`-Adic Boundary Fixed Point `n_∞ = -1 ∉ ℕ`, Odd-Core Seesaw Law,
and Closed-Form `M`-Step Recurrence Solution with Dual-Core Drift Conservation, `0 Prop premises`)**: -/
theorem thm29_collatz_trailing_ones_burn_macro_step
    (steps : List (Int × Int))
    (L1 L2 : List (Int × Int × Int))
    (r0 PR QR PR_next pbeta q0 q1 n1 nInf : Int) :
    let n0    := PR * q0 - 1
    let dMac  := (pbeta * n1 + 1) - QR * q0
    let dn1   := (n1 + 1) - PR_next * q1
    -- 1. M-screw monoid homomorphism across screw lists L1, L2
    --    and stage-exponent telescoping:
    (multiScrewP (L1 ++ L2) = multiScrewP L1 * multiScrewP L2 ∧
     multiScrewQ (L1 ++ L2) = multiScrewQ L1 * multiScrewQ L2 ∧
     multiScrewD (L1 ++ L2) = multiScrewQ L2 * multiScrewD L1 + multiScrewP L1 * multiScrewD L2 ∧
     multiScrewC (L1 ++ L2) = multiScrewP L2 * multiScrewC L1 + multiScrewQ L1 * multiScrewC L2 ∧
     macroSumA steps - macroSumB r0 steps = macroSumBeta steps + macroFinalR r0 steps - r0 ∧
     2 * macroSumA steps - 3 * macroSumB r0 steps =
       macroCatalanDrift r0 steps + 2 * macroFinalR r0 steps - 2 * r0 ∧
     128 * macroSumA steps - 203 * macroSumB r0 steps =
       53 * (2 * macroSumA steps - 3 * macroSumB r0 steps) -
       22 * (2 * macroSumB r0 steps - macroSumA steps) ∧
     128 * macroSumA steps - 203 * macroSumB r0 steps =
       53 * macroCatalanDrift r0 steps +
       22 * (macroSumBeta steps - macroSumB r0 steps) +
       128 * (macroFinalR r0 steps - r0) ∧
     (multiScrewD L1 = multiScrewQ L1 - multiScrewP L1 →
       multiScrewD ((2, 3, 1) :: L1) = multiScrewQ ((2, 3, 1) :: L1) - multiScrewP ((2, 3, 1) :: L1)) ∧
     multiScrewD ((pbeta, 1, 0) :: L1) = pbeta * multiScrewD L1 ∧
     multiScrewP (L1 ++ [(pbeta, 1, 0)]) = multiScrewP L1 * pbeta ∧
     multiScrewQ (L1 ++ [(pbeta, 1, 0)]) = multiScrewQ L1 ∧
     multiScrewD (L1 ++ [(pbeta, 1, 0)]) = multiScrewD L1 ∧
     multiScrewD (L1 ++ [(pbeta, 1, 0), (PR, QR, QR - PR)] ++ L2) -
       multiScrewD (L1 ++ [(PR, QR, QR - PR), (pbeta, 1, 0)] ++ L2) =
       multiScrewP L1 * ((pbeta - 1) * (QR - PR) * multiScrewQ L2)) ∧
    -- 2. Double SL₂(ℤ) Bézout lock, exclusion of the non-natural 2-adic boundary fixed point n_∞ = -1 ∉ ℕ_{≥ 1},
    --    and macro-screw capture:
    ((PR ≠ QR → ((PR - QR) * nInf = QR - PR ↔ nInf = -1)) ∧
     (PR * q0 - n0 = 1) ∧
     ((PR * pbeta) * n1 - QR * n0 - (QR - PR) = PR * dMac) ∧
     ((PR * pbeta) * (n0 - n1) = PR * ((PR * pbeta - QR) * q0 - (pbeta - 1) - dMac))) ∧
    -- 3. Odd-Core transition and single-step dual envelope identity:
    (((pbeta * PR_next) * q1 - QR * q0 - (pbeta - 1) = dMac - pbeta * dn1) ∧
     ((QR + pbeta - 1) * q0 - (pbeta * PR_next) * q1 - (pbeta - 1) * (q0 - 1) = pbeta * dn1 - dMac) ∧
     (PR * pbeta - (QR + pbeta - 1) = (PR - 1) * pbeta - (QR - 1))) := by
  dsimp
  have hP := multiScrewP_append L1 L2
  have hQ := multiScrewQ_append L1 L2
  have hD := multiScrewD_append L1 L2
  have hC : multiScrewC (L1 ++ L2) = multiScrewP L2 * multiScrewC L1 + multiScrewQ L1 * multiScrewC L2 := by
    unfold multiScrewC; rw [hP, hQ]
    simp only [Int.mul_sub, Int.sub_mul, Int.mul_comm, Int.mul_left_comm]; omega
  have hTel1 : ∀ (st : List (Int × Int)) (rInit : Int),
        macroSumA st - macroSumB rInit st = macroSumBeta st + macroFinalR rInit st - rInit := by
    intro st; induction st with
    | nil => intro rInit; dsimp [macroSumA, macroSumB, macroSumBeta, macroFinalR]; omega
    | cons hd tl ih => intro rInit; rcases hd with ⟨b, rN⟩; dsimp [macroSumA, macroSumB, macroSumBeta, macroFinalR]; have := ih rN; omega
  have hTel2 : ∀ (st : List (Int × Int)) (rInit : Int),
        2 * macroSumA st - 3 * macroSumB rInit st = macroCatalanDrift rInit st + 2 * macroFinalR rInit st - 2 * rInit := by
    intro st; induction st with
    | nil => intro rInit; dsimp [macroSumA, macroSumB, macroCatalanDrift, macroFinalR]; omega
    | cons hd tl ih => intro rInit; rcases hd with ⟨b, rN⟩; dsimp [macroSumA, macroSumB, macroCatalanDrift, macroFinalR]; have := ih rN; omega
  refine ⟨⟨hP, hQ, hD, hC, hTel1 steps r0, hTel2 steps r0, by omega,
            by have h1 := hTel1 steps r0; have h2 := hTel2 steps r0; omega,
            by intro hUp; dsimp [multiScrewD, multiScrewQ, multiScrewP]; omega,
            by dsimp [multiScrewD]; omega,
            by rw [multiScrewP_append]; dsimp [multiScrewP]; simp only [Int.mul_one],
            by rw [multiScrewQ_append]; dsimp [multiScrewQ]; omega,
            by rw [multiScrewD_append]; dsimp [multiScrewQ, multiScrewD]; omega,
            by
              rw [multiScrewD_append, multiScrewD_append, multiScrewD_append, multiScrewD_append]
              rw [multiScrewP_append, multiScrewP_append]
              dsimp [multiScrewP, multiScrewQ, multiScrewD]
              simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                         Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add,
                         Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
              omega⟩,
          ⟨?_, by omega,
           by simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
                         Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega,
           by simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
                         Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega⟩,
          ⟨by simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
                         Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega,
           by simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
                         Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega,
           by simp only [Int.sub_mul, Int.one_mul]; omega⟩⟩
  · intro hNe
    constructor
    · intro hEq
      have hZeroProd : (PR - QR) * (nInf + 1) = 0 := by
        have : (PR - QR) * (nInf + 1) = (PR - QR) * nInf - (QR - PR) := by simp only [Int.mul_add, Int.mul_one]; omega
        omega
      cases Int.mul_eq_zero.mp hZeroProd with
      | inl h0 => omega
      | inr h1 => omega
    · intro hMin1; subst hMin1; simp only [Int.mul_neg, Int.mul_one]; omega

end RotatorCalculusPaper
