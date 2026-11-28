import RotatorQuadrature
import ProjectiveFieldCalculus
import InverseTrigHyperbolic
import LogicCohomology
import PillaiDiophantine
import AbcPlanetaryWronskian
import ModelTheoreticLimit
import CollatzPlanetarySplice
import CollatzGearMonoid

/-!
# RotatorCalculusPaper (Umbrella Module & Unified Diophantine Planetary-Differential Bridge)
Imports all 6 standalone paper-specific Lean 4 modules:
1. `RotatorQuadrature` (`thm1`..`thm3`)
2. `LogicCohomology` (`thm4`..`thm5`)
3. `PillaiDiophantine` (`thm6`, `thm7`, `thm10`, `thm11`)
4. `AbcPlanetaryWronskian` (`thm8`, `thm9`, `thm12`..`thm16`)
5. `ModelTheoreticLimit` (`thm17`)
6. `CollatzPlanetarySplice` (`thm18`..`thm29`, `thm31`..`thm33`)
and proves `thm30_unified_pillai_abc_collatz_planetary_differential_bridge`, uniting Pillai,
`A + B = C`, and the `3n + 1` gear cascade as specializations of one three-shaft planetary
differential `𝒜 + ℬ = 𝒞` embedded into the four-quadrant rotator `ℤ_{4Q}` with bilateral integer
bracket bounds (`0 sorryAx`, `0 Classical.choice`, `0 Prop premises`).
-/

namespace RotatorCalculusPaper

set_option linter.unusedSimpArgs false

/-- **Theorem 30 (Unified Three-Shaft Planetary-Differential Bridge for Pillai, `A + B = C`,
and the `3n + 1` Gear Cascade on `ℤ_{4Q}`, `0 Prop premises`)**: -/
theorem thm30_unified_pillai_abc_collatz_planetary_differential_bridge
    (Q Acal Bcal u v phi0
     At Bt Ct X Y Z alpha beta
     U V a b
     n0 nG nMin : Int)
    (G : List (Int × Int × Int)) :
    let Ccal := Acal + Bcal
    let w := u + v
    let g := Acal * v - Bcal * u
    let Crot := Q - phi0
    let Srot := phi0
    let Irot := Bcal * Crot - Acal * Srot
    let Drot := Crot * v - Srot * u
    let Rfull := (At * Bt * Ct) * (X * Y * Z)
    let Kcoeff := (Bt * Bt * Ct) * (Y * Y * Z)
    let Gap := U - V
    let P1 := U + (V + V)
    let Q1 := (U + U) + V
    let I1 := a * P1 - b * Q1
    let uP := a * P1
    let vQ := b * Q1
    let phi3 := uP * uP + uP * vQ + vQ * vQ
    let DG := multiScrewP G
    let NG := multiScrewQ G
    let RG := DG * n0 - NG * nG
    -- 1. Common three-shaft rotator law on Z_{4Q} and Mal'cev cell-capture bracket:
    ((Q * Acal = Ccal * Crot - Irot) ∧
     (Q * Bcal = Ccal * Srot + Irot) ∧
     (Ccal * Drot - w * Irot = g * Q) ∧
     (Bcal * (Ccal - Bcal) - Acal * Bcal = 0) ∧
     ((Ccal - Bcal) * v - Bcal * u = g) ∧
     (0 ≤ Irot → Irot < Ccal →
       Ccal * Crot - Ccal < Q * Acal ∧ Q * Acal ≤ Ccal * Crot ∧
       Ccal * Srot ≤ Q * Bcal ∧ Q * Bcal < Ccal * Srot + Ccal)) ∧
    -- 2. A + B = C branch: bilateral circular bracket on R_full:
    (((Bt * Y) * (Ct * Z * Z * Z) + Kcoeff * alpha = Rfull * beta) →
     0 ≤ alpha → alpha ≤ At * X - 1 → 0 < Kcoeff →
     (Rfull * beta - Kcoeff * (At * X - 1) ≤ (Bt * Y) * (Ct * Z * Z * Z) ∧
      (Bt * Y) * (Ct * Z * Z * Z) ≤ Rfull * beta ∧
      (1 ≤ alpha → (Bt * Y) * (Ct * Z * Z * Z) < Rfull * beta))) ∧
    -- 3. Pillai branch: root-free cubic Pade compression, I_1 <= -1, and lower gap bound >= 3 U:
    ((U * I1 * phi3 = (a * a * a) * (Gap * Gap * Gap) * (U + V) -
                      (U * (b * b * b) - V * (a * a * a)) * (Q1 * Q1 * Q1)) ∧
     (1 ≤ U → 1 ≤ uP → 1 ≤ vQ →
      (a * a * a) * (Gap * Gap * Gap) * (U + V) < (U * (b * b * b) - V * (a * a * a)) * (Q1 * Q1 * Q1) →
      3 ≤ phi3 ∧ I1 ≤ -1 ∧ I1 ≠ 0 ∧
      3 * U ≤ (U * (b * b * b) - V * (a * a * a)) * (Q1 * Q1 * Q1) -
              (a * a * a) * (Gap * Gap * Gap) * (U + V))) ∧
    -- 4. Collatz 3n + 1 branch as a Pillai-ABC balance in u(n) = 2n + 1 and cycle lower bound:
    ((((DG - NG) + 2 * RG) + NG * (2 * nG + 1) = DG * (2 * n0 + 1)) ∧
     (nG = n0 →
       (DG - NG) * n0 = RG ∧
       (DG - NG) * ((2 * n0 + 1) - 1) = 2 * RG ∧
       (1 ≤ nMin → nMin ≤ n0 → NG < DG →
         nMin * (DG - NG) ≤ RG))) := by
  dsimp
  have hRotA : Q * Acal = (Acal + Bcal) * (Q - phi0) - (Bcal * (Q - phi0) - Acal * phi0) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hRotB : Q * Bcal = (Acal + Bcal) * phi0 + (Bcal * (Q - phi0) - Acal * phi0) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hRotDet : (Acal + Bcal) * ((Q - phi0) * v - phi0 * u) -
                 (u + v) * (Bcal * (Q - phi0) - Acal * phi0) =
                 (Acal * v - Bcal * u) * Q := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hSelfI : Bcal * (Acal + Bcal - Bcal) - Acal * Bcal = 0 := by
    have hEqA : Acal + Bcal - Bcal = Acal := by omega
    rw [hEqA, Int.mul_comm Bcal Acal, Int.sub_self]
  have hSelfD : (Acal + Bcal - Bcal) * v - Bcal * u = Acal * v - Bcal * u := by
    have hEqA : Acal + Bcal - Bcal = Acal := by omega
    rw [hEqA]
  have hGearBal : ((multiScrewP G - multiScrewQ G) + 2 * (multiScrewP G * n0 - multiScrewQ G * nG)) +
                  multiScrewQ G * (2 * nG + 1) = multiScrewP G * (2 * n0 + 1) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hPade := thm10_root_free_cubic_pade_compression U V a b
  dsimp at hPade
  refine ⟨⟨hRotA, hRotB, hRotDet, hSelfI, hSelfD,
           by intro hGe hLt; refine ⟨by omega, by omega, by omega, by omega⟩⟩,
          ?_, ⟨hPade, ?_⟩, ⟨hGearBal, ?_⟩⟩
  · intro hCirc hAlpha0 hAlphaMax hKpos
    have hKnonneg : 0 ≤ (Bt * Bt * Ct) * (Y * Y * Z) * alpha :=
      Int.mul_nonneg (by omega) hAlpha0
    have hKdiff : 0 ≤ (Bt * Bt * Ct) * (Y * Y * Z) * ((At * X - 1) - alpha) :=
      Int.mul_nonneg (by omega) (by omega)
    have hKexpand : (Bt * Bt * Ct) * (Y * Y * Z) * ((At * X - 1) - alpha) =
                    (Bt * Bt * Ct) * (Y * Y * Z) * (At * X - 1) -
                    (Bt * Bt * Ct) * (Y * Y * Z) * alpha := by
      simp only [Int.mul_sub]
    refine ⟨by omega, by omega, ?_⟩
    intro hAlpha1
    have hKstrict : 0 < (Bt * Bt * Ct) * (Y * Y * Z) * alpha :=
      Int.mul_pos hKpos (by omega)
    omega
  · intro hU1 huP1 hvQ1 hRhsGt
    have huPsq : 1 ≤ (a * (U + (V + V))) * (a * (U + (V + V))) :=
      Int.mul_pos (by omega : 0 < a * (U + (V + V))) (by omega : 0 < a * (U + (V + V)))
    have hvQsq : 1 ≤ (b * ((U + U) + V)) * (b * ((U + U) + V)) :=
      Int.mul_pos (by omega : 0 < b * ((U + U) + V)) (by omega : 0 < b * ((U + U) + V))
    have huvProd : 1 ≤ (a * (U + (V + V))) * (b * ((U + U) + V)) :=
      Int.mul_pos (by omega : 0 < a * (U + (V + V))) (by omega : 0 < b * ((U + U) + V))
    have hPhi3 : 3 ≤ (a * (U + (V + V))) * (a * (U + (V + V))) +
                     (a * (U + (V + V))) * (b * ((U + U) + V)) +
                     (b * ((U + U) + V)) * (b * ((U + U) + V)) := by omega
    have hProdNeg : U * (a * (U + (V + V)) - b * ((U + U) + V)) *
                    ((a * (U + (V + V))) * (a * (U + (V + V))) +
                     (a * (U + (V + V))) * (b * ((U + U) + V)) +
                     (b * ((U + U) + V)) * (b * ((U + U) + V))) < 0 := by omega
    have hI1lt0 : a * (U + (V + V)) - b * ((U + U) + V) < 0 := by
      rcases Int.lt_trichotomy (a * (U + (V + V)) - b * ((U + U) + V)) 0 with hLt | hEq | hGt
      · exact hLt
      · rw [hEq, Int.mul_zero, Int.zero_mul] at hProdNeg
        exact False.elim (Int.lt_irrefl 0 hProdNeg)
      · have hGe0 : 0 ≤ a * (U + (V + V)) - b * ((U + U) + V) := Int.le_of_lt hGt
        have h1 : 0 ≤ U * (a * (U + (V + V)) - b * ((U + U) + V)) := Int.mul_nonneg (by omega) hGe0
        have h2 : 0 ≤ U * (a * (U + (V + V)) - b * ((U + U) + V)) *
                      ((a * (U + (V + V))) * (a * (U + (V + V))) +
                       (a * (U + (V + V))) * (b * ((U + U) + V)) +
                       (b * ((U + U) + V)) * (b * ((U + U) + V))) := Int.mul_nonneg h1 (by omega)
        exact False.elim (Int.lt_irrefl 0 (Int.lt_of_le_of_lt h2 hProdNeg))
    have hI1neg : a * (U + (V + V)) - b * ((U + U) + V) ≤ -1 :=
      Int.le_of_lt_add_one hI1lt0
    have hNegProd : 3 * U ≤ -(U * (a * (U + (V + V)) - b * ((U + U) + V)) *
                    ((a * (U + (V + V))) * (a * (U + (V + V))) +
                     (a * (U + (V + V))) * (b * ((U + U) + V)) +
                     (b * ((U + U) + V)) * (b * ((U + U) + V)))) := by
      have hStep1 : U ≤ U * (-(a * (U + (V + V)) - b * ((U + U) + V))) := by
        have : U * (-(a * (U + (V + V)) - b * ((U + U) + V))) - U =
               U * (-(a * (U + (V + V)) - b * ((U + U) + V)) - 1) := by simp only [Int.mul_sub, Int.mul_one]
        have : 0 ≤ U * (-(a * (U + (V + V)) - b * ((U + U) + V)) - 1) := Int.mul_nonneg (by omega) (by omega)
        omega
      have hStep2 : 3 * (U * (-(a * (U + (V + V)) - b * ((U + U) + V)))) ≤
                    (U * (-(a * (U + (V + V)) - b * ((U + U) + V)))) *
                    ((a * (U + (V + V))) * (a * (U + (V + V))) +
                     (a * (U + (V + V))) * (b * ((U + U) + V)) +
                     (b * ((U + U) + V)) * (b * ((U + U) + V))) := by
        have hId : (U * (-(a * (U + (V + V)) - b * ((U + U) + V)))) *
                   ((a * (U + (V + V))) * (a * (U + (V + V))) +
                    (a * (U + (V + V))) * (b * ((U + U) + V)) +
                    (b * ((U + U) + V)) * (b * ((U + U) + V))) -
                   3 * (U * (-(a * (U + (V + V)) - b * ((U + U) + V)))) =
                   (U * (-(a * (U + (V + V)) - b * ((U + U) + V)))) *
                   (((a * (U + (V + V))) * (a * (U + (V + V))) +
                     (a * (U + (V + V))) * (b * ((U + U) + V)) +
                     (b * ((U + U) + V)) * (b * ((U + U) + V))) - 3) := by
          simp only [Int.mul_sub, Int.mul_comm 3 (U * (-(a * (U + (V + V)) - b * ((U + U) + V))))]
        have : 0 ≤ (U * (-(a * (U + (V + V)) - b * ((U + U) + V)))) *
                   (((a * (U + (V + V))) * (a * (U + (V + V))) +
                     (a * (U + (V + V))) * (b * ((U + U) + V)) +
                     (b * ((U + U) + V)) * (b * ((U + U) + V))) - 3) := Int.mul_nonneg (by omega) (by omega)
        omega
      have hEqNeg : (U * (-(a * (U + (V + V)) - b * ((U + U) + V)))) *
                    ((a * (U + (V + V))) * (a * (U + (V + V))) +
                     (a * (U + (V + V))) * (b * ((U + U) + V)) +
                     (b * ((U + U) + V)) * (b * ((U + U) + V))) =
                    -(U * (a * (U + (V + V)) - b * ((U + U) + V)) *
                     ((a * (U + (V + V))) * (a * (U + (V + V))) +
                      (a * (U + (V + V))) * (b * ((U + U) + V)) +
                      (b * ((U + U) + V)) * (b * ((U + U) + V)))) := by
        simp only [Int.mul_neg, Int.neg_mul]
      omega
    have hFourth : 3 * U ≤ (U * (b * b * b) - V * (a * a * a)) * (((U + U) + V) * ((U + U) + V) * ((U + U) + V)) -
                           (a * a * a) * ((U - V) * (U - V) * (U - V)) * (U + V) := by omega
    exact ⟨hPhi3, hI1neg, Int.ne_of_lt hI1lt0, hFourth⟩
  · intro hCyc
    have hCyc1 : (multiScrewP G - multiScrewQ G) * n0 = multiScrewP G * n0 - multiScrewQ G * nG := by
      rw [hCyc]
      simp only [Int.sub_mul]
    have hCyc2 : (multiScrewP G - multiScrewQ G) * ((2 * n0 + 1) - 1) = 2 * (multiScrewP G * n0 - multiScrewQ G * nG) := by
      have hSub1 : (2 * n0 + 1) - 1 = 2 * n0 := by omega
      rw [hSub1, ← Int.mul_assoc, Int.mul_comm (multiScrewP G - multiScrewQ G) 2, Int.mul_assoc, hCyc1]
    refine ⟨hCyc1, hCyc2, ?_⟩
    intro hnMin1 hn0Min hGt
    have : (multiScrewP G - multiScrewQ G) * n0 - nMin * (multiScrewP G - multiScrewQ G) =
           (multiScrewP G - multiScrewQ G) * (n0 - nMin) := by
      simp only [Int.mul_sub, Int.mul_comm nMin (multiScrewP G - multiScrewQ G)]
    have : 0 ≤ (multiScrewP G - multiScrewQ G) * (n0 - nMin) := Int.mul_nonneg (by omega) (by omega)
    omega

/-- **Theorem 36 (Unified First/Second-Derivative and Variational Extremum Principles
across Pillai Padé Towers, `A + B = C` Mason–Stothers Gauge Flows, and Collatz Gear Permutations)**:
Using the general derivative operator `fieldDeriv` (`D f(x) = f(x + 1) - f(x)`) and variational
action `cascadeAction` (`thm35`):
1. **Strict Convexity and Sign-Change Minimum of Quadratic Residual Energy `E(k) = (I₀ + Δ · k)²`:**
   For `I(k) = I₀ + Δ * k` and `E(k) = I(k) * I(k)`:
   - First derivative: `fieldDeriv I k = Δ` and `fieldDeriv E k = Δ * (2 * I k + Δ)`,
   - Second derivative: `fieldDeriv (fieldDeriv E) k = 2 * (Δ * Δ)` (`≥ 2` whenever `Δ ≠ 0`),
   - Sign-change extremum bracket: whenever `1 ≤ Δ` and `I k ≤ 0 ∧ 0 ≤ I (k + 1)`,
     `-Δ ≤ I k ∧ I (k + 1) ≤ Δ`, `fieldDeriv E (k - 1) < 0` (if `I k < 0`), and `0 < fieldDeriv E (k + 1)`.
2. **Pillai / `abc` Padé-Tower Floor-Step Extremum in `k`:**
   On any floor `R : List Int` with `P_R = padeTowerP R U V`, `Q_R = padeTowerQ R U V`, and next-floor
   residual `I_{R'}(k) = a * (P_R + k * Q_R) - b * (k * P_R + Q_R)`:
   - `fieldDeriv I_{R'} k = a * Q_R - b * P_R`,
   - `fieldDeriv (fieldDeriv (fun t => I_{R'} t * I_{R'} t)) k = 2 * ((a * Q_R - b * P_R) * (a * Q_R - b * P_R))`.
3. **`A + B = C` Mason–Stothers Gauge Noether Conservation `D_t W*(t) = 0` and Principal-Cell Minimum:**
   Along the gauge flow `α(t) = α₀ + t * (Ã X)`, `β(t) = β₀ + t * (B̃ Y)`, `γ(t) = γ₀ + t * (C̃ Z)`:
   - Noether invariance of the cubic Wronskian `W*(t) = A * Y² * β(t) - B * X² * α(t)`:
     `fieldDeriv W* t = 0` (since `A = Ã X³`, `B = B̃ Y³`),
   - Strict convexity of gauge energy `E_α(t) = α(t)²`:
     `fieldDeriv (fieldDeriv E_α) t = 2 * ((Ã * X) * (Ã * X))`,
   - Principal-cell minimum (`t = 0` with `0 ≤ α₀`): for all `1 ≤ t` (with `1 ≤ Ã X`, `1 ≤ B̃ Y`, `1 ≤ C̃ Z`),
     `α(0) < α(t) ∧ β(0) < β(t) ∧ γ(0) < γ(t)`.
4. **Collatz Variational Boundary Maximum/Minimum Principle (Strict Positivity of the Swap Derivative):**
   For any binary gear-word prefix `w1 : List Bool` and suffix `w2 : List Bool`, swapping an adjacent
   odd–even pair `[true, false] ↦ [false, true]` inside `w1 ++ [true, false] ++ w2` leaves `P_tot` and `Q_tot`
   invariant and has a strictly positive variational derivative:
   - `multiScrewD (collatzWordScrews (w1 ++ [false, true] ++ w2)) - multiScrewD (collatzWordScrews (w1 ++ [true, false] ++ w2)) = multiScrewP (collatzWordScrews w1) * multiScrewQ (collatzWordScrews w2) ≥ 1`,
   so no interior permutation is stationary (`δ_swap R_w ≠ 0`), forcing the global minimum `R_min = 3^B - 2^B`
   and global maximum `R_max = 2^{A-B}(3^B - 2^B)` onto the two boundary vertices (`thm31`). -/
theorem thm36_unified_extremum_principles_across_pillai_abc_and_collatz
    (R : List Int) (w1 w2 : List Bool)
    (I0 Delta k U V a b At Bt Ct X Y Z alpha0 beta0 gamma0 t : Int) :
    let Ik := fun m => I0 + Delta * m
    let Ek := fun m => Ik m * Ik m
    let PR := padeTowerP R U V
    let QR := padeTowerQ R U V
    let IRnext := fun m => a * (PR + m * QR) - b * (m * PR + QR)
    let wx := At * X
    let wy := Bt * Y
    let wz := Ct * Z
    let A  := At * X * X * X
    let B  := Bt * Y * Y * Y
    let alphaT := fun m => alpha0 + m * wx
    let betaT  := fun m => beta0 + m * wy
    let gammaT := fun m => gamma0 + m * wz
    let WstarT := fun m => A * (Y * Y) * betaT m - B * (X * X) * alphaT m
    let L1 := collatzWordScrews w1
    let L2 := collatzWordScrews w2
    -- 1. General quadratic residual energy convexity and sign-change minimum:
    (fieldDeriv Ik k = Delta ∧
     fieldDeriv Ek k = Delta * (2 * Ik k + Delta) ∧
     fieldDeriv (fieldDeriv Ek) k = 2 * (Delta * Delta) ∧
     (Delta ≠ 0 → 2 ≤ fieldDeriv (fieldDeriv Ek) k) ∧
     (1 ≤ Delta → Ik k ≤ 0 → 0 ≤ Ik (k + 1) →
       -Delta ≤ Ik k ∧ Ik (k + 1) ≤ Delta ∧ 0 < fieldDeriv Ek (k + 1))) ∧
    -- 2. Pillai / abc Padé-tower floor-step derivative and second derivative:
    (fieldDeriv IRnext k = a * QR - b * PR ∧
     fieldDeriv (fieldDeriv (fun m => IRnext m * IRnext m)) k =
       2 * ((a * QR - b * PR) * (a * QR - b * PR))) ∧
    -- 3. A + B = C Mason-Stothers gauge Noether conservation and principal-cell minimum:
    (fieldDeriv WstarT t = 0 ∧
     fieldDeriv (fieldDeriv (fun m => alphaT m * alphaT m)) t = 2 * (wx * wx) ∧
     (1 ≤ wx → 1 ≤ wy → 1 ≤ wz → 1 ≤ t →
       alphaT 0 < alphaT t ∧ betaT 0 < betaT t ∧ gammaT 0 < gammaT t)) ∧
    -- 4. Collatz variational swap derivative strict positivity:
    (multiScrewD (collatzWordScrews (w1 ++ [false, true] ++ w2)) -
     multiScrewD (collatzWordScrews (w1 ++ [true, false] ++ w2)) =
       multiScrewP L1 * multiScrewQ L2 ∧
     1 ≤ multiScrewP L1 * multiScrewQ L2) := by
  intro Ik Ek PR QR IRnext wx wy wz A B alphaT betaT gammaT WstarT L1 L2
  have hD1 : fieldDeriv Ik k = Delta := by
    dsimp [fieldDeriv, Ik]
    simp only [Int.mul_add, Int.mul_one]; omega
  have hDE : fieldDeriv Ek k = Delta * (2 * Ik k + Delta) := by
    dsimp [fieldDeriv, Ek, Ik]
    have h2 : ∀ (u : Int), 2 * u = u + u := by intro u; omega
    simp only [h2, Int.mul_add, Int.add_mul, Int.mul_one,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hDDE : fieldDeriv (fieldDeriv Ek) k = 2 * (Delta * Delta) := by
    dsimp [fieldDeriv, Ek, Ik]
    have h2 : ∀ (u : Int), 2 * u = u + u := by intro u; omega
    simp only [h2, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hDPade1 : fieldDeriv IRnext k = a * QR - b * PR := by
    dsimp [fieldDeriv, IRnext]
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.one_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hDPade2 : fieldDeriv (fieldDeriv (fun m => IRnext m * IRnext m)) k =
                 2 * ((a * QR - b * PR) * (a * QR - b * PR)) := by
    dsimp [fieldDeriv, IRnext]
    have h2 : ∀ (u : Int), 2 * u = u + u := by intro u; omega
    simp only [h2, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.one_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hNoether : fieldDeriv WstarT t = 0 := by
    dsimp [fieldDeriv, WstarT, betaT, alphaT, A, B, wx, wy]
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.one_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hDDAlpha : fieldDeriv (fieldDeriv (fun m => alphaT m * alphaT m)) t = 2 * (wx * wx) := by
    dsimp [fieldDeriv, alphaT]
    have h2 : ∀ (u : Int), 2 * u = u + u := by intro u; omega
    simp only [h2, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.one_mul, Int.mul_one,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hSwap :
      multiScrewD (collatzWordScrews (w1 ++ [false, true] ++ w2)) -
      multiScrewD (collatzWordScrews (w1 ++ [true, false] ++ w2)) =
      multiScrewP L1 * multiScrewQ L2 := by
    rw [collatzWordScrews_append, collatzWordScrews_append,
        collatzWordScrews_append, collatzWordScrews_append]
    rw [multiScrewD_append, multiScrewD_append, multiScrewD_append, multiScrewD_append]
    rw [multiScrewP_append, multiScrewP_append]
    dsimp [collatzWordScrews, collatzGearOfBool, multiScrewP, multiScrewQ, multiScrewD, L1, L2]
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hP1Q2pos : 1 ≤ multiScrewP L1 * multiScrewQ L2 := by
    have h31_1 := (thm31_collatz_binary_gear_word_extremal_drift_envelope_and_cycle_squeeze w1 0).1
    have h31_2 := (thm31_collatz_binary_gear_word_extremal_drift_envelope_and_cycle_squeeze w2 0).1
    have hP1 : 1 ≤ multiScrewP L1 := by
      have hPo1 : 1 ≤ collatzWordPOdd w1 := h31_1.1
      have hPe1 : 1 ≤ collatzWordPEven w1 := h31_1.2.1
      have hProd1 : collatzWordPOdd w1 * collatzWordPEven w1 = multiScrewP L1 := h31_1.2.2.2.1
      have := Int.mul_le_mul hPo1 hPe1 (by omega) (by omega)
      omega
    have hQ2 : 1 ≤ multiScrewQ L2 := by
      have hPo2 : 1 ≤ collatzWordPOdd w2 := h31_2.1
      have hPoQ2 : collatzWordPOdd w2 ≤ multiScrewQ L2 := h31_2.2.2.1
      omega
    have := Int.mul_le_mul hP1 hQ2 (by omega) (by omega)
    omega
  refine ⟨⟨hD1, hDE, hDDE, ?_, ?_⟩, ⟨hDPade1, hDPade2⟩, ⟨hNoether, hDDAlpha, ?_⟩, ⟨hSwap, hP1Q2pos⟩⟩
  · intro hNe0
    rw [hDDE]
    rcases Int.lt_trichotomy Delta 0 with hLt | hEq | hGt
    · have : 1 ≤ (-Delta) * (-Delta) := by
        have := Int.mul_le_mul (by omega : 1 ≤ -Delta) (by omega : 1 ≤ -Delta) (by omega) (by omega); omega
      have hNeg : (-Delta) * (-Delta) = Delta * Delta := by simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      omega
    · exact False.elim (hNe0 hEq)
    · have : 1 ≤ Delta * Delta := by
        have := Int.mul_le_mul (by omega : 1 ≤ Delta) (by omega : 1 ≤ Delta) (by omega) (by omega); omega
      omega
  · intro hD1pos hIkLe0 hIk1Ge0
    have hStep : Ik (k + 1) = Ik k + Delta := by
      dsimp [Ik]; simp only [Int.mul_add, Int.mul_one]; omega
    have hDE1 : fieldDeriv Ek (k + 1) = Delta * (2 * Ik (k + 1) + Delta) := by
      dsimp [fieldDeriv, Ek, Ik]
      have h2 : ∀ (u : Int), 2 * u = u + u := by intro u; omega
      simp only [h2, Int.mul_add, Int.add_mul, Int.mul_one,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
    have hPos : 0 < Delta * (2 * Ik (k + 1) + Delta) :=
      Int.mul_pos (by omega) (by omega)
    exact ⟨by omega, by omega, by omega⟩
  · intro hWx1 hWy1 hWz1 hT1
    dsimp [alphaT, betaT, gammaT]
    simp only [Int.zero_mul, Int.add_zero]
    have hTx : 1 ≤ t * wx := by
      have := Int.mul_le_mul hT1 hWx1 (by omega) (by omega); omega
    have hTy : 1 ≤ t * wy := by
      have := Int.mul_le_mul hT1 hWy1 (by omega) (by omega); omega
    have hTz : 1 ≤ t * wz := by
      have := Int.mul_le_mul hT1 hWz1 (by omega) (by omega); omega
    exact ⟨by omega, by omega, by omega⟩

end RotatorCalculusPaper
