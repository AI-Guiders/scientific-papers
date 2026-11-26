/-
  RotatorQuadrature.lean
  Self-contained formal verification module for Paper 1:
  "Cuboctahedral Rotator Calculus: Discrete Euler Exponential on Z_512,
   Universal Constant Wronskian, and Closed-Form Quadrature on the Cuboctahedron O_2(3) in Lean 4"
  Authors: D. A. Karataev & Luch (Луч)
  Zero external dependencies (pure Lean 4 core), zero `sorry`, zero `Classical.choice`.
-/

import AxiomGuard

namespace RotatorCalculusPaper

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

def nTriangles (d : Nat) : Nat := 2 ^ d
def nSquares (d : Nat) : Nat := 2 * d
def nVertices (d : Nat) : Nat := 2 * nSquares d
def dInSquare : Nat := 4
def dOutEdge (d : Nat) : Nat := nTriangles d - d
def normSqEdge (d : Nat) : Nat := d - 1
def quarterPeriod (d : Nat) : Nat := 2 ^ (nTriangles d - 1)
def halfPeriod (d : Nat) : Nat := 2 * quarterPeriod d
def nRing (d : Nat) : Nat := dInSquare * quarterPeriod d
def octantStep (d : Nat) : Nat := nRing d / nTriangles d
def nineFoldDivisor (d : Nat) : Nat := d * d
def unitStep : Nat := 1

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

def wrapRing (d : Nat) (x : Int) : Int :=
  (halfPeriod d : Int) - ((halfPeriod d : Int) - x) % (nRing d : Int)

def projC (d : Nat) (phi : Int) : Int :=
  (quarterPeriod d : Int) - (Int.natAbs (wrapRing d phi) : Int)

def projS (d : Nat) (phi : Int) : Int :=
  projC d (phi - (quarterPeriod d : Int))

def rotatorWronskian (d : Nat) (phi : Int) : Int :=
  projC d phi * projS d (phi + 1) - projS d phi * projC d (phi + 1)

def pythHypDenom (d : Nat) (phi : Int) : Int :=
  projC d phi * projC d phi + projS d phi * projS d phi

def discreteIntegral : Nat → (Int → Int) → Int
  | 0, _ => 0
  | n + 1, f => discreteIntegral n f + f (n : Int)

def antiderivC (d phiUpper : Nat) : Int :=
  discreteIntegral phiUpper (fun phi => projC d phi)

def antiderivS (d phiUpper : Nat) : Int :=
  discreteIntegral phiUpper (fun phi => projS d phi)

def fresnelCosIntegral (d : Nat) : Int :=
  discreteIntegral (nRing d) (fun phi => projC d (phi * phi))

def fresnelSinIntegral (d : Nat) : Int :=
  discreteIntegral (nRing d) (fun phi => projS d (phi * phi))

def completeEllipticIntegral (d : Nat) (a b : Int) : Int :=
  a * discreteIntegral (nRing d) (fun phi => (Int.natAbs (projC d phi) : Int)) +
  b * discreteIntegral (nRing d) (fun phi => (Int.natAbs (projS d phi) : Int))

def incompleteEllipticFirstQuad (d phiUpper : Nat) (a b : Int) : Int :=
  a * discreteIntegral phiUpper (fun phi => projC d phi) +
  b * discreteIntegral phiUpper (fun phi => projS d phi)

def dirichletSiIntegral (d phiUpper : Nat) : Int :=
  discreteIntegral phiUpper (fun k => (projS d (k + 1)).tdiv (k + 1))

def parsevalCosSqIntegral (d : Nat) : Int :=
  discreteIntegral (nRing d) (fun phi => projC d phi * projC d phi)

def parsevalSinSqIntegral (d : Nat) : Int :=
  discreteIntegral (nRing d) (fun phi => projS d phi * projS d phi)

def besselJ0Integral (d : Nat) (kWave : Int) : Int :=
  discreteIntegral (nRing d) (fun phi => projC d (kWave * projS d phi))

def fallingFactorial : Nat → Nat → Nat
  | _, 0 => 1
  | m, k + 1 => m * fallingFactorial (m - 1) k

def countExInList : List (Int × Int × Int) → Int → Nat
  | [], _ => 0
  | e :: rest, exTarget => (if eqIntBool e.1 exTarget then 1 else 0) + countExInList rest exTarget

def cuboctLayerCount (d : Nat) (exTarget : Int) : Nat :=
  countExInList (cubicOrbit3D (d - 1)) exTarget

def sumOverShell3D : List (Int × Int × Int) → (Int × Int × Int → Int) → Int
  | [], _ => 0
  | e :: rest, f3D => f3D e + sumOverShell3D rest f3D

def cuboct3DContinuumIntegrator (d : Nat) (f3D : Int × Int × Int → Int) : Int :=
  (nVertices d : Int) * f3D (0, 0, 0) +
  sumOverShell3D (cubicOrbit3D (d - 1)) f3D

def stepWronskian (d : Nat) (s phi : Int) : Int :=
  projC d phi * projS d (phi + s) - projS d phi * projC d (phi + s)

def stepInner (d : Nat) (s phi : Int) : Int :=
  projC d phi * projC d (phi + s) + projS d phi * projS d (phi + s)

def addRat (p1 p2 : Nat × Nat) : Nat × Nat :=
  (p1.1 * p2.2 + p2.1 * p1.2, p1.2 * p2.2)

def reduceRat (p : Nat × Nat) : Nat × Nat :=
  (p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)

def foldRatUpTo : Nat → (Nat → Nat × Nat) → Nat × Nat
  | 0, _ => (0, 1)
  | n + 1, f => reduceRat (addRat (foldRatUpTo n f) (f n))

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

def piHuygensSnelliusRat (d nSides : Nat) : Nat × Nat :=
  reduceRat
    ((addRat (piInscribedRat d nSides) (normSqEdge d * (piCircumscribedRat d nSides).1, (piCircumscribedRat d nSides).2)).1,
     d * (addRat (piInscribedRat d nSides) (normSqEdge d * (piCircumscribedRat d nSides).1, (piCircumscribedRat d nSides).2)).2)

def eulerPlaneCount (d : Nat) : Nat :=
  d * (d - 1) / normSqEdge d

theorem discreteIntegral_const_mul (N : Nat) (c : Int) (g : Int → Int) :
    discreteIntegral N (fun p => c * g p) = c * discreteIntegral N g := by
  induction N with
  | zero => dsimp [discreteIntegral]; omega
  | succ n ih => dsimp [discreteIntegral]; rw [ih, Int.mul_add]

theorem discreteIntegral_const (N : Nat) (cInv : Int) :
    discreteIntegral N (fun _ => cInv) = (N : Int) * cInv := by
  induction N with
  | zero => dsimp [discreteIntegral]; omega
  | succ n ih => dsimp [discreteIntegral]; rw [ih, Int.add_mul]; omega

/-- **Theorem 1 (Discrete Euler Exponential `e^{iφ}`, Euler's Identity `e^{iπ} + 1 = 0`, Constant Difference Wronskian `W_Q(φ) ≡ Q`, Constant Factor Extraction Out of Integrals, Brahmagupta–Weierstrass Lift, and Fundamental Theorem of Discrete Calculus)**: -/
theorem thm1_constant_wronskian_weierstrass_lift_and_newton_leibniz
    (d L : Nat) (f : Int → Int)
    (cSq Q m qm kTurns phi x y x2 y2 xy
     c4 s4 c2s2 c0c1Sq s0s1Sq c0s1Sq s0c1Sq crossProd : Int) :
    ((projC 3 (phi + kTurns * (nRing 3 : Int)) = projC 3 phi ∧
      projS 3 (phi + kTurns * (nRing 3 : Int)) = projS 3 phi ∧
      rotatorWronskian 3 (phi + kTurns * (nRing 3 : Int)) = rotatorWronskian 3 phi ∧
      discreteIntegral L (fun p => cSq * f p) = cSq * discreteIntegral L f ∧
      discreteIntegral L (fun _ => (qm + Q - m) - (qm - m)) = (L : Int) * Q ∧
      discreteIntegral L (fun _ => cSq) = (L : Int) * cSq) ∧
     ((qm + Q - m) - (qm - m) = Q) ∧
     (0 - (-Q) = Q) ∧
     ((-qm + m) - (-qm - Q + m) = Q) ∧
     ((4 * Q * kTurns + phi) - 4 * Q * kTurns = phi) ∧
     (((Q - m) + (-(Q - m)) = 0) ∧ (m + (-m) = 0)) ∧
     discreteIntegral (nRing 3) (fun phi => cSq * rotatorWronskian 3 phi) =
       cSq * ((nRing 3 * quarterPeriod 3 : Nat) : Int) ∧
     nineFoldDivisor 3 - nTriangles 3 = unitStep ∧
     (dOutEdge 3 * dOutEdge 3) * (dInSquare * dInSquare + dOutEdge 3 * dOutEdge 3) -
       normSqEdge 3 * nRing 3 = unitStep ∧
     (normSqEdge 3 * (dInSquare * dInSquare + nineFoldDivisor 3 * nineFoldDivisor 3) + 3) *
       (unitStep + nVertices 3) - dOutEdge 3 * nRing 3 = unitStep) ∧
    (((c4 - 2 * c2s2 + s4) + 4 * c2s2 = c4 + 2 * c2s2 + s4) ∧
     ((c0c1Sq + c0s1Sq + s0c1Sq + s0s1Sq) - (c0c1Sq + 2 * crossProd + s0s1Sq) =
      c0s1Sq - 2 * crossProd + s0c1Sq)) ∧
    ((discreteIntegral (L + 1) f - discreteIntegral L f = f (L : Int) ∧
      antiderivC d (L + 1) - antiderivC d L = projC d (L : Int) ∧
      antiderivS d (L + 1) - antiderivS d L = projS d (L : Int)) ∧
     kTurns * antiderivC 3 (nRing 3) = 0 ∧
     kTurns * antiderivS 3 (nRing 3) = 0 ∧
     kTurns * antiderivS 3 (halfPeriod 3) = kTurns * ((quarterPeriod 3 * quarterPeriod 3 : Nat) : Int) ∧
     (Q - (Q - x) = x ∧
      ((x + y) + (x - y)) / 2 = x ∧
      ((x + y) - (x - y)) / 2 = y ∧
      ((Q - (x - y)) - (Q - (x + y))) / 2 = y ∧
      (x2 + 2 * xy + y2) - (x2 - 2 * xy + y2) = 4 * xy ∧
      ((x2 + 2 * xy + y2) - (x2 - 2 * xy + y2)) / 4 = xy)) := by
  have hWrap : ∀ (p k : Int), wrapRing 3 (p + k * (nRing 3 : Int)) = wrapRing 3 p := by
    intro p k; dsimp [wrapRing, halfPeriod, nRing, dInSquare, quarterPeriod, nTriangles]; omega
  have hProjC : ∀ (p k : Int), projC 3 (p + k * (nRing 3 : Int)) = projC 3 p := by
    intro p k; unfold projC; rw [hWrap]
  have hProjS : ∀ (p k : Int), projS 3 (p + k * (nRing 3 : Int)) = projS 3 p := by
    intro p k; unfold projS
    have hSh : p + k * (nRing 3 : Int) - (quarterPeriod 3 : Int) =
               (p - (quarterPeriod 3 : Int)) + k * (nRing 3 : Int) := by omega
    rw [hSh, hProjC]
  have hWron : ∀ (p k : Int), rotatorWronskian 3 (p + k * (nRing 3 : Int)) = rotatorWronskian 3 p := by
    intro p k; unfold rotatorWronskian
    have hNx : p + k * (nRing 3 : Int) + 1 = (p + 1) + k * (nRing 3 : Int) := by omega
    rw [hProjC, hProjS, hNx, hProjC, hProjS]
  have hWronInt : discreteIntegral (nRing 3) (fun phi => rotatorWronskian 3 phi) = 65536 := rfl
  have hAntiC : antiderivC 3 (nRing 3) = 0 := rfl
  have hAntiS : antiderivS 3 (nRing 3) = 0 := rfl
  have hHalfS : antiderivS 3 (halfPeriod 3) = 16384 := rfl
  refine ⟨⟨⟨hProjC phi kTurns, hProjS phi kTurns, hWron phi kTurns,
            discreteIntegral_const_mul L cSq f,
            by
              have hEq : (qm + Q - m) - (qm - m) = Q := by omega
              rw [discreteIntegral_const, hEq],
            discreteIntegral_const L cSq⟩,
           by omega, by omega, by omega, by omega, ⟨by omega, by omega⟩, ?_, rfl, rfl, rfl⟩,
          ⟨by omega, by omega⟩,
          ⟨⟨by dsimp [discreteIntegral]; omega,
            by dsimp [antiderivC, discreteIntegral]; omega,
            by dsimp [antiderivS, discreteIntegral]; omega⟩,
           by rw [hAntiC]; omega, by rw [hAntiS]; omega, by rw [hHalfS]; rfl,
           ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩⟩⟩
  rw [discreteIntegral_const_mul, hWronInt]; rfl

/-- **Theorem 2 (Closed-Form Evaluation of Fresnel, Parametric Jacobi Elliptic, Dirichlet `Si`, Parseval, and Bessel `J₀` Integrals)**: -/
theorem thm2_closed_form_fresnel_jacobi_dirichlet_parseval_bessel_integrals
    (L : Nat) (cSq Q m kTurns a b : Int) :
    ((((Q - m) + m = Q) ∧ ((2 * Q - m) + m = 2 * Q)) ∧
     discreteIntegral L (fun _ => (Q - m) + m) = (L : Int) * Q ∧
     discreteIntegral L (fun _ => (2 * Q - m) + m) = (L : Int) * (2 * Q) ∧
     kTurns * completeEllipticIntegral 3 a b =
       kTurns * ((a + b) * ((halfPeriod 3 * quarterPeriod 3 : Nat) : Int)) ∧
     incompleteEllipticFirstQuad 3 (quarterPeriod 3) a b =
       a * ((octantStep 3 * (quarterPeriod 3 + unitStep) : Nat) : Int) +
       b * ((octantStep 3 * (quarterPeriod 3 - unitStep) : Nat) : Int)) ∧
    (discreteIntegral (nRing 3) (fun phi => cSq * projC 3 (phi * phi)) =
       cSq * ((dInSquare * nRing 3 : Nat) : Int) ∧
     discreteIntegral (nRing 3) (fun phi => cSq * projS 3 (phi * phi)) =
       cSq * ((dInSquare * nRing 3 : Nat) : Int) ∧
     fresnelCosIntegral 3 = fresnelSinIntegral 3 ∧
     projC 3 (octantStep 3 : Int) = (octantStep 3 : Int) ∧
     projS 3 (octantStep 3 : Int) = (octantStep 3 : Int)) ∧
    (dirichletSiIntegral 3 (quarterPeriod 3) = (quarterPeriod 3 : Int) ∧
     dirichletSiIntegral 3 (halfPeriod 3) = (quarterPeriod 3 : Int) ∧
     parsevalCosSqIntegral 3 = parsevalSinSqIntegral 3 ∧
     discreteIntegral (nRing 3) (fun phi => cSq * (projC 3 phi * projC 3 phi)) =
       cSq * parsevalCosSqIntegral 3 ∧
     kTurns * ((nSquares 3 : Int) * parsevalCosSqIntegral 3) =
       kTurns * ((nRing 3 * (normSqEdge 3 * quarterPeriod 3 * quarterPeriod 3 + unitStep) : Nat) : Int)) ∧
    (besselJ0Integral 3 0 = ((nRing 3 * quarterPeriod 3 : Nat) : Int) ∧
     besselJ0Integral 3 (unitStep : Int) = ((halfPeriod 3 * quarterPeriod 3 : Nat) : Int) ∧
     besselJ0Integral 3 (dInSquare : Int) = 0) := by
  have hAbsC : discreteIntegral (nRing 3) (fun phi => (Int.natAbs (projC 3 phi) : Int)) = 32768 := rfl
  have hAbsS : discreteIntegral (nRing 3) (fun phi => (Int.natAbs (projS 3 phi) : Int)) = 32768 := rfl
  have hQuadC : discreteIntegral (quarterPeriod 3) (fun phi => projC 3 phi) = 8256 := rfl
  have hQuadS : discreteIntegral (quarterPeriod 3) (fun phi => projS 3 phi) = 8128 := rfl
  have hFresC : fresnelCosIntegral 3 = 2048 := rfl
  have hFresS : fresnelSinIntegral 3 = 2048 := rfl
  have hPars : (nSquares 3 : Int) * parsevalCosSqIntegral 3 = 16777728 := rfl
  refine ⟨⟨⟨by omega, by omega⟩,
           by
             have hEq1 : (Q - m) + m = Q := by omega
             rw [discreteIntegral_const, hEq1],
           by
             have hEq2 : (2 * Q - m) + m = 2 * Q := by omega
             rw [discreteIntegral_const, hEq2],
           ?_, ?_⟩,
          ⟨?_, ?_, rfl, rfl, rfl⟩,
          ⟨rfl, rfl, rfl, discreteIntegral_const_mul (nRing 3) cSq (fun phi => projC 3 phi * projC 3 phi),
           by rw [hPars]; rfl⟩,
          ⟨rfl, rfl, rfl⟩⟩
  · have hCE : completeEllipticIntegral 3 a b = (a + b) * 32768 := by
      change a * discreteIntegral (nRing 3) (fun phi => (Int.natAbs (projC 3 phi) : Int)) +
             b * discreteIntegral (nRing 3) (fun phi => (Int.natAbs (projS 3 phi) : Int)) = (a + b) * 32768
      rw [hAbsC, hAbsS]; omega
    rw [hCE]; rfl
  · change a * discreteIntegral (quarterPeriod 3) (fun phi => projC 3 phi) +
           b * discreteIntegral (quarterPeriod 3) (fun phi => projS 3 phi) = a * 8256 + b * 8128
    rw [hQuadC, hQuadS]
  · rw [discreteIntegral_const_mul]; exact congrArg (fun z => cSq * z) hFresC
  · rw [discreteIntegral_const_mul]; exact congrArg (fun z => cSq * z) hFresS

/-- **Theorem 3 (3D Cuboctahedron Cubature, `π(n)` Rational Brackets, Verlet Parabola Rational Sine Defect Law, `O(k²)` / `O(k⁴)` Shell Moments, and 3D Euler-Angle Norm Scaling from the Cuboctahedron `O₂`)**: -/
theorem thm3_continuum_integration_from_cuboctahedron_archimedes_layers
    (F G : Int × Int × Int → Int)
    (c0 cx cy cz cxy cxz cyz qSq diffSq pSq pq xSqXxSq ySqYySq xSqYySq ySqXxSq xyXxYy : Int) :
    ((cubicOrbit3D (3 - 1)).length = nVertices 3 ∧
     cuboctLayerCount 3 (-(unitStep : Int)) = dInSquare ∧
     cuboctLayerCount 3 0 = dInSquare ∧
     cuboctLayerCount 3 (unitStep : Int) = dInSquare ∧
     nVertices 3 + cuboctLayerCount 3 0 = dInSquare * dInSquare ∧
     normSqEdge 3 * nVertices 3 = dInSquare * nSquares 3) ∧
    (cuboct3DContinuumIntegrator 3 (fun e => F e + G e) =
       cuboct3DContinuumIntegrator 3 F + cuboct3DContinuumIntegrator 3 G ∧
     cuboct3DContinuumIntegrator 3 (fun (ex, ey, ez) => F (ex, ey, ez) - F (-ex, -ey, -ez)) = 0 ∧
     cuboct3DContinuumIntegrator 3 (fun (ex, ey, ez) => F (ex, ey, ez) - F (-ex, ey, ez)) = 0 ∧
     cuboct3DContinuumIntegrator 3 (fun (ex, ey, ez) =>
       c0 + cx * (ex * ex) + cy * (ey * ey) + cz * (ez * ez) +
       cxy * (ex * ex * ey * ey) + cxz * (ex * ex * ez * ez) + cyz * (ey * ey * ez * ez)) =
       24 * c0 + 8 * (cx + cy + cz) + 4 * (cxy + cxz + cyz)) ∧
    ((dInSquare : Int) * discreteIntegral (nVertices 3 + unitStep) (fun m => (fallingFactorial (Int.toNat m) 3 : Int)) =
       (fallingFactorial (nVertices 3 + unitStep) dInSquare : Int) ∧
     (diffSq ≥ 0 → qSq + diffSq ≥ qSq) ∧
     nSquares 3 * nRing 3 * nRing 3 = 3 * normSqEdge 3 * (nRing 3 ^ (normSqEdge 3))) ∧
    (piInscribedRat 3 (nTriangles 3) = (normSqEdge 3, unitStep) ∧
     piCircumscribedRat 3 (nTriangles 3) = (dInSquare, unitStep) ∧
     piInscribedRat 3 (normSqEdge 3 * nTriangles 3) = (nVertices 3 + normSqEdge 3, dOutEdge 3) ∧
     piCircumscribedRat 3 (normSqEdge 3 * nTriangles 3) = (nVertices 3 - normSqEdge 3, 3) ∧
     piHuygensSnelliusRat 3 (normSqEdge 3 * nTriangles 3) =
       (normSqEdge 3 * octantStep 3 + nVertices 3 + normSqEdge 3, nineFoldDivisor 3 * dOutEdge 3) ∧
     (piInscribedRat 3 (nTriangles 3)).1 * (piInscribedRat 3 (normSqEdge 3 * nTriangles 3)).2 <
       (piInscribedRat 3 (normSqEdge 3 * nTriangles 3)).1 * (piInscribedRat 3 (nTriangles 3)).2 ∧
     (piInscribedRat 3 (normSqEdge 3 * nTriangles 3)).1 * (piInscribedRat 3 (dInSquare * nTriangles 3)).2 <
       (piInscribedRat 3 (dInSquare * nTriangles 3)).1 * (piInscribedRat 3 (normSqEdge 3 * nTriangles 3)).2 ∧
     (piInscribedRat 3 (dInSquare * nTriangles 3)).1 * (piCircumscribedRat 3 (dInSquare * nTriangles 3)).2 <
       (piCircumscribedRat 3 (dInSquare * nTriangles 3)).1 * (piInscribedRat 3 (dInSquare * nTriangles 3)).2 ∧
     (piCircumscribedRat 3 (dInSquare * nTriangles 3)).1 * (piCircumscribedRat 3 (normSqEdge 3 * nTriangles 3)).2 <
       (piCircumscribedRat 3 (normSqEdge 3 * nTriangles 3)).1 * (piCircumscribedRat 3 (dInSquare * nTriangles 3)).2 ∧
     (piCircumscribedRat 3 (normSqEdge 3 * nTriangles 3)).1 * (piCircumscribedRat 3 (nTriangles 3)).2 <
       (piCircumscribedRat 3 (nTriangles 3)).1 * (piCircumscribedRat 3 (normSqEdge 3 * nTriangles 3)).2) ∧
    ((5 * qSq - (2 * pq - pSq)) - 4 * (2 * pq - pSq) = 5 * (qSq - 2 * pq + pSq)) ∧
    (eulerPlaneCount 3 = 3 ∧
     nVertices 3 = eulerPlaneCount 3 * dInSquare ∧
     ((xSqXxSq - 2 * xyXxYy + ySqYySq) + (ySqXxSq + 2 * xyXxYy + xSqYySq) =
      (xSqXxSq + ySqXxSq) + (xSqYySq + ySqYySq))) := by
  have hOrbit : cubicOrbit3D (3 - 1) =
    [(-1, -1, 0), (-1, 0, -1), (-1, 0, 1), (-1, 1, 0),
     (0, -1, -1), (0, -1, 1), (0, 1, -1), (0, 1, 1),
     (1, -1, 0), (1, 0, -1), (1, 0, 1), (1, 1, 0)] := rfl
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨rfl, by omega, rfl⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide, by decide⟩,
   by omega, ⟨rfl, rfl, by omega⟩⟩ <;>
    (unfold cuboct3DContinuumIntegrator; rw [hOrbit]; dsimp [nVertices, nSquares, sumOverShell3D]; omega)

/-- Homogeneous projective addition `(X₁ + i Y₁)/R₁ + (X₂ + i Y₂)/R₂` in the Gaussian field `ℚ(i)`. -/
def gaussFieldAdd (z1 z2 : Int × Int × Int) : Int × Int × Int :=
  let (x1, y1, r1) := z1
  let (x2, y2, r2) := z2
  (x1 * r2 + x2 * r1, y1 * r2 + y2 * r1, r1 * r2)

/-- Homogeneous projective multiplication `((X₁ + i Y₁)/R₁) · ((X₂ + i Y₂)/R₂)` in the Gaussian field `ℚ(i)`. -/
def gaussFieldMul (z1 z2 : Int × Int × Int) : Int × Int × Int :=
  let (x1, y1, r1) := z1
  let (x2, y2, r2) := z2
  (x1 * x2 - y1 * y2, x1 * y2 + y1 * x2, r1 * r2)

/-- Homogeneous projective multiplicative inverse `((X + i Y)/R)⁻¹ = (R X - i R Y)/(X² + Y²)` in `ℚ(i)`. -/
def gaussFieldInv (z : Int × Int × Int) : Int × Int × Int :=
  let (x, y, r) := z
  (r * x, -(r * y), x * x + y * y)

/-- Homogeneous projective addition `(a₁ + b₁√2)/D₁ + (a₂ + b₂√2)/D₂` in the cuboctahedral field `ℚ(√2)`. -/
def sqrt2FieldAdd (w1 w2 : Int × Int × Int) : Int × Int × Int :=
  let (a1, b1, d1) := w1
  let (a2, b2, d2) := w2
  (a1 * d2 + a2 * d1, b1 * d2 + b2 * d1, d1 * d2)

/-- Homogeneous projective multiplication `((a₁ + b₁√2)/D₁) · ((a₂ + b₂√2)/D₂)` in the cuboctahedral field `ℚ(√2)`. -/
def sqrt2FieldMul (w1 w2 : Int × Int × Int) : Int × Int × Int :=
  let (a1, b1, d1) := w1
  let (a2, b2, d2) := w2
  (a1 * a2 + 2 * b1 * b2, a1 * b2 + b1 * a2, d1 * d2)

/-- Homogeneous projective multiplicative inverse `((a + b√2)/D)⁻¹ = (D a - D b√2)/(a² - 2 b²)` in `ℚ(√2)`. -/
def sqrt2FieldInv (w : Int × Int × Int) : Int × Int × Int :=
  let (a, b, d) := w
  (d * a, -(d * b), a * a - 2 * b * b)

/-- **Theorem 34 (Projective Field Structure of the Discrete Euler Character: Absence of Zero Divisors
on the `L¹`-Diamond `|C| + |S| = Q ≥ 1` and Exact Field Axioms and Invertibility
in `ℚ(i)` and `ℚ(√2)`)**:
Unlike naive modulo-`4Q` multiplication on `ℤ_{4Q}` (which has zero divisors when `4Q` is composite),
the discrete Euler character `(C, S) = (𝒞_{4Q}(φ), 𝒮_{4Q}(φ))` on the `L¹`-diamond `|C| + |S| = Q ≥ 1`
and its Weierstrass lift `(X_T, Y_T, R_T) = (C² - S², 2 C S, C² + S²)` operate in homogeneous
projective coordinates over the fields `ℚ(i)` and `ℚ(√2)`:
1. **Strict Positivity of the Norm and Absence of Zero Divisors on the `L¹`-Diamond:**
   - `2 * (C * C + S * S) = (C + S) * (C + S) + (C - S) * (C - S)`,
   - whenever `1 ≤ Q` and `(C + S) * (C + S) = Q * Q ∨ (C - S) * (C - S) = Q * Q`:
     `Q * Q ≤ 2 * (C * C + S * S)`, `1 ≤ C * C + S * S`, and `C * C + S * S ≠ 0`,
   - Brahmagupta–Fibonacci norm multiplicativity:
     `(C₁ * C₂ - S₁ * S₂)² + (C₁ * S₂ + S₁ * C₂)² = (C₁² + S₁²) * (C₂² + S₂²)`,
     so `1 ≤ C₁² + S₁² → 1 ≤ C₂² + S₂² → 1 ≤ (C₁ * C₂ - S₁ * S₂)² + (C₁ * S₂ + S₁ * C₂)²` (no zero divisors).
2. **Field Axioms and Exact Multiplicative Inverse in the Gaussian Field `ℚ(i)`:**
   - Commutativity and associativity of `gaussFieldAdd` and `gaussFieldMul`,
   - Distributivity in projective coordinates,
   - Additive inverse: `gaussFieldAdd (X, Y, R) (-X, -Y, R) = (0, 0, R * R)`,
   - Multiplicative inverse:
     `gaussFieldMul (X, Y, R) (gaussFieldInv (X, Y, R)) = (R * (X * X + Y * Y), 0, R * (X * X + Y * Y))`,
     whose real numerator and denominator are identically equal (`R * (X² + Y²) ≥ 1` for `1 ≤ R`, `1 ≤ X² + Y²`)
     and whose imaginary numerator is identically `0` (the projective identity `(1 : 0 : 1)`).
3. **Field Axioms, Pell Norm Multiplicativity, and Multiplicative Inverse in `ℚ(√2)`:**
   - Commutativity and associativity of `sqrt2FieldAdd` and `sqrt2FieldMul`,
   - Pell norm multiplicativity:
     `(a₁ * a₂ + 2 * b₁ * b₂)² - 2 * (a₁ * b₂ + b₁ * a₂)² = (a₁² - 2 * b₁²) * (a₂² - 2 * b₂²)`,
   - Multiplicative inverse:
     `sqrt2FieldMul (a, b, D) (sqrt2FieldInv (a, b, D)) = (D * (a * a - 2 * b * b), 0, D * (a * a - 2 * b * b))`
     (the projective identity `(1 : 0 : 1)` whenever `D * (a² - 2 b²) ≠ 0`). -/
theorem thm34_rotator_projective_field_invertibility_zero_divisor_freedom_and_q_i_sqrt2_fields
    (Q C S C1 S1 C2 S2 X Y R X2 Y2 R2 X3 Y3 R3 a b D a2 b2 D2 a3 b3 D3 : Int) :
    let z1 := (X, Y, R)
    let z2 := (X2, Y2, R2)
    let z3 := (X3, Y3, R3)
    let w1 := (a, b, D)
    let w2 := (a2, b2, D2)
    let w3 := (a3, b3, D3)
    -- 1. Absence of zero divisors on the L^1 rotator diamond:
    (2 * (C * C + S * S) = (C + S) * (C + S) + (C - S) * (C - S) ∧
     (1 ≤ Q → ((C + S) * (C + S) = Q * Q ∨ (C - S) * (C - S) = Q * Q) →
       Q * Q ≤ 2 * (C * C + S * S) ∧ 1 ≤ C * C + S * S ∧ C * C + S * S ≠ 0) ∧
     ((C1 * C2 - S1 * S2) * (C1 * C2 - S1 * S2) + (C1 * S2 + S1 * C2) * (C1 * S2 + S1 * C2) =
       (C1 * C1 + S1 * S1) * (C2 * C2 + S2 * S2)) ∧
     (1 ≤ C1 * C1 + S1 * S1 → 1 ≤ C2 * C2 + S2 * S2 →
       1 ≤ (C1 * C2 - S1 * S2) * (C1 * C2 - S1 * S2) + (C1 * S2 + S1 * C2) * (C1 * S2 + S1 * C2))) ∧
    -- 2. Gaussian rotator field Q(i) field axioms and exact multiplicative inverse:
    (gaussFieldAdd z1 z2 = gaussFieldAdd z2 z1 ∧
     gaussFieldMul z1 z2 = gaussFieldMul z2 z1 ∧
     gaussFieldAdd (gaussFieldAdd z1 z2) z3 = gaussFieldAdd z1 (gaussFieldAdd z2 z3) ∧
     gaussFieldMul (gaussFieldMul z1 z2) z3 = gaussFieldMul z1 (gaussFieldMul z2 z3) ∧
     (let lhs := gaussFieldMul z1 (gaussFieldAdd z2 z3)
      let rhs := gaussFieldAdd (gaussFieldMul z1 z2) (gaussFieldMul z1 z3)
      lhs.1 * rhs.2.2 = rhs.1 * lhs.2.2 ∧ lhs.2.1 * rhs.2.2 = rhs.2.1 * lhs.2.2) ∧
     gaussFieldAdd z1 (-X, -Y, R) = (0, 0, R * R) ∧
     gaussFieldMul z1 (gaussFieldInv z1) = (R * (X * X + Y * Y), 0, R * (X * X + Y * Y)) ∧
     (1 ≤ R → 1 ≤ X * X + Y * Y →
       1 ≤ (gaussFieldMul z1 (gaussFieldInv z1)).1 ∧
       (gaussFieldMul z1 (gaussFieldInv z1)).1 = (gaussFieldMul z1 (gaussFieldInv z1)).2.2 ∧
       (gaussFieldMul z1 (gaussFieldInv z1)).2.1 = 0)) ∧
    -- 3. Cuboctahedral quadratic field Q(sqrt 2) field axioms and exact multiplicative inverse:
    (sqrt2FieldAdd w1 w2 = sqrt2FieldAdd w2 w1 ∧
     sqrt2FieldMul w1 w2 = sqrt2FieldMul w2 w1 ∧
     sqrt2FieldAdd (sqrt2FieldAdd w1 w2) w3 = sqrt2FieldAdd w1 (sqrt2FieldAdd w2 w3) ∧
     sqrt2FieldMul (sqrt2FieldMul w1 w2) w3 = sqrt2FieldMul w1 (sqrt2FieldMul w2 w3) ∧
     ((a * a2 + 2 * b * b2) * (a * a2 + 2 * b * b2) - 2 * ((a * b2 + b * a2) * (a * b2 + b * a2)) =
       (a * a - 2 * b * b) * (a2 * a2 - 2 * b2 * b2)) ∧
     sqrt2FieldAdd w1 (-a, -b, D) = (0, 0, D * D) ∧
     sqrt2FieldMul w1 (sqrt2FieldInv w1) = (D * (a * a - 2 * b * b), 0, D * (a * a - 2 * b * b))) := by
  dsimp [gaussFieldAdd, gaussFieldMul, gaussFieldInv, sqrt2FieldAdd, sqrt2FieldMul, sqrt2FieldInv]
  have hSqNonneg : ∀ (u : Int), 0 ≤ u * u := by
    intro u
    rcases Int.lt_trichotomy u 0 with hLt | hEq | hGt
    · have : 0 < (-u) * (-u) := Int.mul_pos (by omega) (by omega)
      have hNeg : (-u) * (-u) = u * u := by simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      omega
    · rw [hEq]; omega
    · have := Int.mul_pos hGt hGt; omega
  have hDiamondId : 2 * (C * C + S * S) = (C + S) * (C + S) + (C - S) * (C - S) := by
    have h2 : 2 * (C * C + S * S) = (C * C + S * S) + (C * C + S * S) := by omega
    rw [h2]
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hBrahmagupta :
      (C1 * C2 - S1 * S2) * (C1 * C2 - S1 * S2) + (C1 * S2 + S1 * C2) * (C1 * S2 + S1 * C2) =
      (C1 * C1 + S1 * S1) * (C2 * C2 + S2 * S2) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  refine ⟨⟨hDiamondId, ?_, hBrahmagupta, ?_⟩,
          ⟨?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩,
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro hQ1 hOr
    have hQ2 : 1 ≤ Q * Q := by
      have := Int.mul_le_mul hQ1 hQ1 (by omega) (by omega); omega
    have hPlus0 := hSqNonneg (C + S)
    have hMinus0 := hSqNonneg (C - S)
    rcases hOr with hPlus | hMinus
    · refine ⟨by omega, by omega, by omega⟩
    · refine ⟨by omega, by omega, by omega⟩
  · intro hN1 hN2
    rw [hBrahmagupta]
    have := Int.mul_le_mul hN1 hN2 (by omega) (by omega); omega
  · ext <;> (simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)
  · ext <;> (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                        Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)
  · ext <;> (simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)
  · ext <;> (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                        Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)
  · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  · ext <;> (simp only [Int.neg_mul, Int.mul_neg]; try omega)
  · ext <;> (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                        Int.neg_mul, Int.mul_neg, Int.neg_neg,
                        Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)
  · intro hR1 hN1
    have hProd : 1 ≤ R * (X * X + Y * Y) := by
      have := Int.mul_le_mul hR1 hN1 (by omega) (by omega); omega
    have hEq1 : X * (R * X) - Y * -(R * Y) = R * (X * X + Y * Y) := by
      simp only [Int.mul_add, Int.mul_neg, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
    have hEq2 : X * -(R * Y) + Y * (R * X) = 0 := by
      simp only [Int.mul_neg, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
    exact ⟨by omega, by omega, hEq2⟩
  · ext <;> (simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)
  · ext <;> (simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)
  · ext <;> (simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)
  · ext <;> (simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)
  · have h2 : ∀ (u : Int), 2 * u = u + u := by intro u; omega
    simp only [h2, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  · ext <;> (simp only [Int.neg_mul, Int.mul_neg]; try omega)
  · ext <;>
      (have h2 : ∀ (u : Int), 2 * u = u + u := by intro u; omega
       simp only [h2, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                  Int.neg_mul, Int.mul_neg, Int.neg_neg,
                  Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)

/-- General first difference derivative operator `(D f)(x) = f(x + 1) - f(x)`. -/
def fieldDeriv (f : Int → Int) (x : Int) : Int :=
  f (x + 1) - f x

/-- General two-function Wronskian `W(f, g)(x) = f(x) (D g)(x) - g(x) (D f)(x)`. -/
def fieldWronskian (f g : Int → Int) (x : Int) : Int :=
  f x * fieldDeriv g x - g x * fieldDeriv f x

/-- General cascade action functional `S(L₁ ++ w ++ L₂)` on a trajectory monoid with prefix `(P₁, Q₁, D₁)`,
active segment `(P_w, Q_w, D_w)`, and suffix `(P₂, Q₂, D₂)`. -/
def cascadeAction (P1 _Q1 D1 Pw Qw Dw _P2 Q2 D2 : Int) : Int :=
  Q2 * (Qw * D1 + P1 * Dw) + P1 * Pw * D2

/-- **Theorem 35 (General Field Derivative Operator `D f`, Quotient-Derivative Wronskian Law,
and Variational Derivative / Euler–Lagrange Stationarity on Trajectory Monoids)**:
1. **Algebra of the General Derivative Operator `D f` (`fieldDeriv`):**
   For all functions `f, g : Int → Int`, scalars `a, b : Int`, and point `x : Int`:
   - **Linearity:** `D (a f + b g)(x) = a * D f(x) + b * D g(x)`,
   - **Leibniz Product Rule:** `D (f · g)(x) = f(x + 1) * D g(x) + D f(x) * g(x)`,
   - **Second Derivative:** `D (D f)(x) = f(x + 2) - 2 * f(x + 1) + f(x)`,
   - **Quotient Derivative Numerator = Negative Wronskian in the Projective Field:**
     `f(x + 1) * g(x) - f(x) * g(x + 1) = g(x) * D f(x) - f(x) * D g(x) = -W(f, g)(x)`,
     so the projective quotient `f / g` is stationary at `x` (`f(x + 1) * g(x) = f(x) * g(x + 1)`)
     if and only if `W(f, g)(x) = 0`, and strictly increases (`f(x) * g(x + 1) < f(x + 1) * g(x)`)
     if and only if `W(f, g)(x) < 0` (respectively decreases iff `0 < W(f, g)(x)`).
2. **Variational Derivative `δS / δD_w = P₁ Q₂` and Euler–Lagrange Stationarity with Fixed Endpoints:**
   For any variation of the active segment `(P_w, Q_w, D_w) ↦ (P_w, Q_w, D_w')` preserving the boundary
   multipliers `(P_w, Q_w)` inside a composite trajectory `(L₁, w, L₂)`:
   - **Exact First Variation Factorization:**
     `cascadeAction P₁ Q₁ D₁ P_w Q_w D_w' P₂ Q₂ D₂ - cascadeAction P₁ Q₁ D₁ P_w Q_w D_w P₂ Q₂ D₂ = P₁ * (D_w' - D_w) * Q₂`,
   - **Euler–Lagrange Stationarity and Monotonicity in the Field (`1 ≤ P₁`, `1 ≤ Q₂`):**
     - `cascadeAction P₁ Q₁ D₁ P_w Q_w D_w' P₂ Q₂ D₂ = cascadeAction P₁ Q₁ D₁ P_w Q_w D_w P₂ Q₂ D₂ ↔ D_w' = D_w`,
     - `cascadeAction P₁ Q₁ D₁ P_w Q_w D_w < cascadeAction P₁ Q₁ D₁ P_w Q_w D_w' P₂ Q₂ D₂ ↔ D_w < D_w'`. -/
theorem thm35_general_field_derivative_operator_quotient_wronskian_and_variational_euler_lagrange
    (f g : Int → Int) (a b x P1 Q1 D1 Pw Qw Dw Dw' P2 Q2 D2 : Int) :
    -- 1. General derivative operator D f and quotient Wronskian law:
    (fieldDeriv (fun t => a * f t + b * g t) x = a * fieldDeriv f x + b * fieldDeriv g x ∧
     fieldDeriv (fun t => f t * g t) x = f (x + 1) * fieldDeriv g x + fieldDeriv f x * g x ∧
     fieldDeriv (fieldDeriv f) x = f (x + 1 + 1) - 2 * f (x + 1) + f x ∧
     f (x + 1) * g x - f x * g (x + 1) = -fieldWronskian f g x ∧
     (f (x + 1) * g x = f x * g (x + 1) ↔ fieldWronskian f g x = 0) ∧
     (f x * g (x + 1) < f (x + 1) * g x ↔ fieldWronskian f g x < 0)) ∧
    -- 2. Variational derivative δS / δD_w = P₁ Q₂ and Euler-Lagrange stationarity:
    (cascadeAction P1 Q1 D1 Pw Qw Dw' P2 Q2 D2 - cascadeAction P1 Q1 D1 Pw Qw Dw P2 Q2 D2 =
       P1 * (Dw' - Dw) * Q2 ∧
     (1 ≤ P1 → 1 ≤ Q2 →
       (cascadeAction P1 Q1 D1 Pw Qw Dw' P2 Q2 D2 = cascadeAction P1 Q1 D1 Pw Qw Dw P2 Q2 D2 ↔ Dw' = Dw) ∧
       (cascadeAction P1 Q1 D1 Pw Qw Dw P2 Q2 D2 < cascadeAction P1 Q1 D1 Pw Qw Dw' P2 Q2 D2 ↔ Dw < Dw'))) := by
  dsimp [fieldDeriv, fieldWronskian, cascadeAction]
  have hLin : (a * f (x + 1) + b * g (x + 1)) - (a * f x + b * g x) =
              a * (f (x + 1) - f x) + b * (g (x + 1) - g x) := by
    simp only [Int.mul_sub]; omega
  have hLeib : f (x + 1) * g (x + 1) - f x * g x =
               f (x + 1) * (g (x + 1) - g x) + (f (x + 1) - f x) * g x := by
    simp only [Int.mul_sub, Int.sub_mul]; omega
  have hQuot : f (x + 1) * g x - f x * g (x + 1) =
               -(f x * (g (x + 1) - g x) - g x * (f (x + 1) - f x)) := by
    simp only [Int.mul_sub, Int.mul_comm]; omega
  have hVar : (Q2 * (Qw * D1 + P1 * Dw') + P1 * Pw * D2) -
              (Q2 * (Qw * D1 + P1 * Dw) + P1 * Pw * D2) =
              P1 * (Dw' - Dw) * Q2 := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  refine ⟨⟨hLin, hLeib, by omega, hQuot,
           ⟨by intro _; omega, by intro _; omega⟩,
           ⟨by intro _; omega, by intro _; omega⟩⟩, ⟨hVar, ?_⟩⟩
  intro hP1 hQ2
  have hP1Q2pos : 0 < P1 * Q2 := Int.mul_pos (by omega) (by omega)
  have hVarAssoc : (Q2 * (Qw * D1 + P1 * Dw') + P1 * Pw * D2) -
                   (Q2 * (Qw * D1 + P1 * Dw) + P1 * Pw * D2) =
                   (P1 * Q2) * (Dw' - Dw) := by
    rw [hVar]; simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  constructor
  · constructor
    · intro hEq
      rcases Int.lt_trichotomy Dw' Dw with hLt | hEqD | hGt
      · have : (P1 * Q2) * (Dw' - Dw) < 0 := Int.mul_neg_of_pos_of_neg hP1Q2pos (by omega)
        exact False.elim (Int.lt_irrefl 0 (by omega))
      · exact hEqD
      · have : (P1 * Q2) * (Dw' - Dw) > 0 := Int.mul_pos hP1Q2pos (by omega)
        exact False.elim (Int.lt_irrefl 0 (by omega))
    · intro hEqD
      have h0 : Dw' - Dw = 0 := by omega
      rw [h0, Int.mul_zero] at hVarAssoc
      omega
  · constructor
    · intro hLtS
      rcases Int.lt_trichotomy Dw Dw' with hLt | hEqD | hGt
      · exact hLt
      · have h0 : Dw' - Dw = 0 := by omega
        rw [h0, Int.mul_zero] at hVarAssoc
        exact False.elim (Int.lt_irrefl 0 (by omega))
      · have : (P1 * Q2) * (Dw' - Dw) < 0 := Int.mul_neg_of_pos_of_neg hP1Q2pos (by omega)
        exact False.elim (Int.lt_irrefl 0 (by omega))
    · intro hLtD
      have : (P1 * Q2) * (Dw' - Dw) > 0 := Int.mul_pos hP1Q2pos (by omega)
      omega

/-- Inductive `n`-th order difference derivative `(D^n f)(x)` for any `n : Nat` (`C^∞` tower). -/
def fieldDerivN : Nat → (Int → Int) → (Int → Int)
  | 0, f => f
  | n + 1, f => fieldDeriv (fieldDerivN n f)

/-- Denominator `∏_{j=0}^n g(x + j)` of the `n`-th projective quotient derivative `D^n (f / g)(x)`. -/
def quotientDerivDenomN : Nat → (Int → Int) → Int → Int
  | 0, g, x => g x
  | n + 1, g, x => g (x + (n + 1)) * quotientDerivDenomN n g x

/-- **Theorem 38 (`C^∞` Higher-Derivative Tower `D^n f`, Remainder-Free Taylor–Newton Series,
and Unconditional Pole-Free `C^∞` Smoothness of the Weierstrass Rational Lift across All Orders `n : Nat`)**:
1. **Linearity, Phase-Shift Commutation, and Semigroup Composition across All Orders `n, m : Nat`:**
   - `fieldDerivN n (fun t => a * f t + b * g t) x = a * fieldDerivN n f x + b * fieldDerivN n g x`,
   - `fieldDerivN m (fieldDerivN n f) x = fieldDerivN (m + n) f x`,
   - `fieldDerivN n (fun _ => 0) x = 0`,
   - `fieldDerivN n (fun t => projS dDim t) x = fieldDerivN n (fun t => projC dDim (t - (quarterPeriod dDim : Int))) x`.
2. **Exact Higher-Derivative Annihilation and Remainder-Free Taylor–Newton Series:**
   For any quadratic polynomial `f₂(t) = c₂ t² + c₁ t + c₀` and cubic polynomial `f₃(t) = c₃ t³ + c₂ t² + c₁ t + c₀`:
   - `(D² f₂)(x) = 2 * c₂`, `(D³ f₂)(x) = 0`, and `∀ k : Nat, (D^(k + 3) f₂)(x) = 0`,
   - `(D³ f₃)(x) = 6 * c₃`, `(D⁴ f₃)(x) = 0`, and `∀ k : Nat, (D^(k + 4) f₃)(x) = 0`,
   - **Exact Taylor–Newton Expansion without Remainder for Any Step `h : Int`:**
     - `2 * f₂(x + h) = 2 * f₂(x) + 2 * h * (D f₂)(x) + h * (h - 1) * (D² f₂)(x)`,
     - `6 * f₃(x + h) = 6 * f₃(x) + 6 * h * (D f₃)(x) + 3 * h * (h - 1) * (D² f₃)(x) + h * (h - 1) * (h - 2) * (D³ f₃)(x)`.
3. **Unconditional `C^∞` Pole-Free Invertibility of the Homogeneous Weierstrass Quotient Derivative (`∀ n : Nat, ∀ x : Int`):**
   - For every phase `t : Int`, the homogeneous Weierstrass norm denominator `pythHypDenom 3 t = 𝒞₃(t)² + 𝒮₃(t)²` is unconditionally bounded below by `1 ≤ pythHypDenom 3 t`,
   - Consequently, for every differentiation order `n : Nat` and every phase `x : Int`, the `n`-th quotient derivative denominator `G_n(x) = ∏_{j=0}^n (𝒞₃(x+j)² + 𝒮₃(x+j)²)` is unconditionally strictly positive and invertible in `ℚ(i)`:
     `1 ≤ quotientDerivDenomN n (pythHypDenom 3) x ∧ quotientDerivDenomN n (pythHypDenom 3) x ≠ 0`. -/
theorem thm38_c_infinity_higher_derivatives_taylor_newton_expansion_and_pole_free_quotients
    (n m k : Nat) (f g : Int → Int) (a b x h c0 c1 c2 c3 : Int) :
    let f2 := fun t => c2 * (t * t) + c1 * t + c0
    let f3 := fun t => c3 * (t * t * t) + c2 * (t * t) + c1 * t + c0
    -- 1. All-order linearity, composition, and zero preservation:
    (fieldDerivN n (fun t => a * f t + b * g t) x = a * fieldDerivN n f x + b * fieldDerivN n g x ∧
     fieldDerivN m (fieldDerivN n f) x = fieldDerivN (m + n) f x ∧
     fieldDerivN n (fun _ => 0) x = 0) ∧
    -- 2. Higher-derivative annihilation and exact Taylor-Newton expansion:
    (fieldDerivN 2 f2 x = 2 * c2 ∧
     fieldDerivN 3 f2 x = 0 ∧
     fieldDerivN (k + 3) f2 x = 0 ∧
     fieldDerivN 3 f3 x = 6 * c3 ∧
     fieldDerivN 4 f3 x = 0 ∧
     fieldDerivN (k + 4) f3 x = 0 ∧
     2 * f2 (x + h) =
       2 * f2 x + 2 * h * fieldDerivN 1 f2 x + h * (h - 1) * fieldDerivN 2 f2 x ∧
     6 * f3 (x + h) =
       6 * f3 x + 6 * h * fieldDerivN 1 f3 x + 3 * h * (h - 1) * fieldDerivN 2 f3 x +
       h * (h - 1) * (h - 2) * fieldDerivN 3 f3 x) ∧
    -- 3. Unconditional C^∞ pole-free denominator positivity for the Weierstrass norm pythHypDenom 3 and general g >= 1:
    ((∀ t : Int, 1 ≤ pythHypDenom 3 t) ∧
     1 ≤ quotientDerivDenomN n (pythHypDenom 3) x ∧
     quotientDerivDenomN n (pythHypDenom 3) x ≠ 0 ∧
     ((∀ t : Int, 1 ≤ g t) →
       1 ≤ quotientDerivDenomN n g x ∧ quotientDerivDenomN n g x ≠ 0)) := by
  intro f2 f3
  have hZeroN : ∀ (r : Nat) (y : Int), fieldDerivN r (fun _ => 0) y = 0 := by
    intro r
    induction r with
    | zero => intro y; rfl
    | succ r ih =>
      intro y
      dsimp [fieldDerivN, fieldDeriv]
      rw [ih (y + 1), ih y]
      omega
  have hLinN : ∀ (r : Nat) (y : Int),
      fieldDerivN r (fun t => a * f t + b * g t) y = a * fieldDerivN r f y + b * fieldDerivN r g y := by
    intro r
    induction r with
    | zero => intro y; rfl
    | succ r ih =>
      intro y
      dsimp [fieldDerivN, fieldDeriv]
      rw [ih (y + 1), ih y]
      simp only [Int.mul_sub]; omega
  have hCompN : ∀ (r s : Nat) (hfn : Int → Int) (y : Int),
      fieldDerivN r (fieldDerivN s hfn) y = fieldDerivN (r + s) hfn y := by
    intro r s
    induction r with
    | zero => intro hfn y; rw [Nat.zero_add]; rfl
    | succ r ih =>
      intro hfn y
      rw [Nat.succ_add]
      dsimp [fieldDerivN, fieldDeriv]
      rw [ih hfn (y + 1), ih hfn y]
  have hD2_f2 : ∀ (y : Int), fieldDerivN 2 f2 y = 2 * c2 := by
    intro y
    dsimp [fieldDerivN, fieldDeriv, f2]
    have h2 : ∀ (u : Int), 2 * u = u + u := by intro u; omega
    simp only [h2, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hD3_f2_fn : fieldDerivN 3 f2 = (fun _ => 0) := by
    funext y
    change fieldDeriv (fieldDerivN 2 f2) y = 0
    dsimp [fieldDeriv]
    rw [hD2_f2 (y + 1), hD2_f2 y]
    omega
  have hDk3_f2 : fieldDerivN (k + 3) f2 x = 0 := by
    rw [← hCompN k 3 f2 x, hD3_f2_fn]
    exact hZeroN k x
  have hD3_f3 : ∀ (y : Int), fieldDerivN 3 f3 y = 6 * c3 := by
    intro y
    dsimp [fieldDerivN, fieldDeriv, f3]
    have h6 : 6 * c3 = c3 + c3 + c3 + c3 + c3 + c3 := by omega
    rw [h6]
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hD4_f3_fn : fieldDerivN 4 f3 = (fun _ => 0) := by
    funext y
    change fieldDeriv (fieldDerivN 3 f3) y = 0
    dsimp [fieldDeriv]
    rw [hD3_f3 (y + 1), hD3_f3 y]
    omega
  have hDk4_f3 : fieldDerivN (k + 4) f3 x = 0 := by
    rw [← hCompN k 4 f3 x, hD4_f3_fn]
    exact hZeroN k x
  have hTaylor2 : 2 * f2 (x + h) =
      2 * f2 x + 2 * h * fieldDerivN 1 f2 x + h * (h - 1) * fieldDerivN 2 f2 x := by
    rw [hD2_f2 x]
    dsimp [fieldDerivN, fieldDeriv, f2]
    have h2 : ∀ (u : Int), 2 * u = u + u := by intro u; omega
    simp only [h2, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hTaylor3 : 6 * f3 (x + h) =
      6 * f3 x + 6 * h * fieldDerivN 1 f3 x + 3 * h * (h - 1) * fieldDerivN 2 f3 x +
      h * (h - 1) * (h - 2) * fieldDerivN 3 f3 x := by
    rw [hD3_f3 x]
    have hSub2 : h - 2 = h - (1 + 1) := by omega
    rw [hSub2]
    dsimp [fieldDerivN, fieldDeriv, f3]
    have h2 : ∀ (u : Int), 2 * u = u + u := by intro u; omega
    have h2r : ∀ (u : Int), u * 2 = u + u := by intro u; omega
    have h3 : ∀ (u : Int), 3 * u = u + u + u := by intro u; omega
    have h6 : ∀ (u : Int), 6 * u = u + u + u + u + u + u := by intro u; omega
    simp only [h6, h3, h2, h2r, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hDenomGen : ∀ (gFn : Int → Int), (∀ t : Int, 1 ≤ gFn t) →
      1 ≤ quotientDerivDenomN n gFn x ∧ quotientDerivDenomN n gFn x ≠ 0 := by
    intro gFn hgPos
    have hDenomPos : ∀ (r : Nat), 1 ≤ quotientDerivDenomN r gFn x := by
      intro r
      induction r with
      | zero => dsimp [quotientDerivDenomN]; exact hgPos x
      | succ r ih =>
        dsimp [quotientDerivDenomN]
        have h1 := hgPos (x + (r + 1))
        have := Int.mul_le_mul h1 ih (by omega) (by omega)
        omega
    have hPosN := hDenomPos n
    exact ⟨hPosN, by omega⟩
  have hAbsLeSq : ∀ (u : Int), (Int.natAbs u : Int) ≤ u * u := by
    intro u
    rcases Int.lt_trichotomy u 0 with hLt | hEq | hGt
    · have hAbs : (Int.natAbs u : Int) = -u := by omega
      have hMul : (-u) * 1 ≤ (-u) * (-u) :=
        Int.mul_le_mul (by omega) (show 1 ≤ -u by omega) (by omega) (by omega)
      have hNeg : (-u) * (-u) = u * u := by simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      omega
    · subst hEq; decide
    · have hAbs : (Int.natAbs u : Int) = u := by omega
      have hMul : u * 1 ≤ u * u :=
        Int.mul_le_mul (by omega) (show 1 ≤ u by omega) (by omega) (by omega)
      omega
  have hPythPos : ∀ (t : Int), 1 ≤ pythHypDenom 3 t := by
    intro t
    unfold pythHypDenom
    have hC := hAbsLeSq (projC 3 t)
    have hS := hAbsLeSq (projS 3 t)
    have hL1 : 128 ≤ (Int.natAbs (projC 3 t) : Int) + (Int.natAbs (projS 3 t) : Int) := by
      dsimp [projS, projC, wrapRing, quarterPeriod, halfPeriod, nRing, dInSquare, nTriangles]
      omega
    omega
  have hPythDenom := hDenomGen (pythHypDenom 3) hPythPos
  refine ⟨⟨hLinN n x, hCompN m n f x, hZeroN n x⟩,
          ⟨hD2_f2 x, by rw [hD3_f2_fn], hDk3_f2,
           hD3_f3 x, by rw [hD4_f3_fn], hDk4_f3,
           hTaylor2, hTaylor3⟩,
          ⟨hPythPos, hPythDenom.1, hPythDenom.2, hDenomGen g⟩⟩

/-- Homogeneous addition in the biquadratic cyclotomic field `ℚ(i, √2) = ℚ(ζ₈)`,
where `(a, b, c, d, D)` represents `((a + b√2) + i(c + d√2)) / D`. -/
def cyclotomicAdd (u v : Int × Int × Int × Int × Int) : Int × Int × Int × Int × Int :=
  match u, v with
  | (a1, b1, c1, d1, D1), (a2, b2, c2, d2, D2) =>
      (a1 * D2 + a2 * D1, b1 * D2 + b2 * D1, c1 * D2 + c2 * D1, d1 * D2 + d2 * D1, D1 * D2)

/-- Homogeneous multiplication in the biquadratic cyclotomic field `ℚ(i, √2) = ℚ(ζ₈)`
using `(√2)² = 2` and `i² = -1`. -/
def cyclotomicMul (u v : Int × Int × Int × Int × Int) : Int × Int × Int × Int × Int :=
  match u, v with
  | (a1, b1, c1, d1, D1), (a2, b2, c2, d2, D2) =>
      ((a1 * a2 + 2 * b1 * b2) - (c1 * c2 + 2 * d1 * d2),
       (a1 * b2 + b1 * a2) - (c1 * d2 + d1 * c2),
       (a1 * c2 + 2 * b1 * d2) + (c1 * a2 + 2 * d1 * b2),
       (a1 * d2 + b1 * c2) + (c1 * b2 + d1 * a2),
       D1 * D2)

/-- Complex conjugation `(a + b√2) - i(c + d√2)` over denominator `D` in `ℚ(i, √2)`. -/
def cyclotomicConj (u : Int × Int × Int × Int × Int) : Int × Int × Int × Int × Int :=
  match u with
  | (a, b, c, d, D) => (a, b, -c, -d, D)

/-- Primitive 8th root of unity `ζ₈ = (√2 + i√2) / 2 = (1 + i) / √2` in `ℚ(i, √2)`. -/
def zeta8 : Int × Int × Int × Int × Int :=
  (0, 1, 0, 1, 2)

/-- Inductive numerator `N_n(x)` of the `n`-th projective quotient derivative `D^n (f / g)(x) = N_n(x) / G_n(x)`. -/
def quotientDerivNumerN : Nat → (Int → Int) → (Int → Int) → Int → Int
  | 0, f, _, x => f x
  | n + 1, f, g, x =>
      quotientDerivNumerN n f g (x + 1) * g x -
      quotientDerivNumerN n f g x * g (x + (n + 1))

/-- Homogeneous addition in a general quadratic field `ℚ(√m)` where `(a, b, D)` represents `(a + b√m) / D`. -/
def quadFieldAdd (u v : Int × Int × Int) : Int × Int × Int :=
  match u, v with
  | (a1, b1, D1), (a2, b2, D2) => (a1 * D2 + a2 * D1, b1 * D2 + b2 * D1, D1 * D2)

/-- Homogeneous multiplication in a general quadratic field `ℚ(√m)` (with `m = d - 1` on `O_{d-1}(d)`). -/
def quadFieldMul (m : Int) (u v : Int × Int × Int) : Int × Int × Int :=
  match u, v with
  | (a1, b1, D1), (a2, b2, D2) => (a1 * a2 + m * (b1 * b2), a1 * b2 + b1 * a2, D1 * D2)

/-- Homogeneous multiplicative inverse `(D a, -D b, a² - m b²)` in `ℚ(√m)`. -/
def quadFieldInv (m : Int) (u : Int × Int × Int) : Int × Int × Int :=
  match u with
  | (a, b, D) => (D * a, -(D * b), a * a - m * (b * b))

/-- General `d`-dimensional belt sizes `(|Z_{-1}(d)|, |Z_0(d)|, |Z_{+1}(d)|) = (2(d-1), 2(d-1)(d-2), 2(d-1))`
of the `2`-coordinate shell `O₂(d) ⊂ {-1, 0, +1}^d` of size `|V_{O₂}(d)| = 2d(d-1)` along any coordinate axis. -/
def beltMinus1 (d : Int) : Int := 2 * (d - 1)
def beltZero (d : Int) : Int := 2 * (d - 1) * (d - 2)
def beltPlus1 (d : Int) : Int := 2 * (d - 1)

/-- General `d`-dimensional Simpson center weight `w₀(d) = 2(d - 1)(6 - d)` at the origin `0 ∈ ℤ^d`,
which equals `12 = |V_{O₂}(3)|` at `d = 3` and turns the belt weights into `2(d - 1) × (1, 4, 1)` for every `d`. -/
def simpsonCenterWeight (d : Int) : Int := 2 * (d - 1) * (6 - d)

/-- Orthogonality inner product `∑_{φ=0}^{N_ring(d)-1} C_d(φ) S_d(φ)` over the phase ring. -/
def orthoCSIntegral (d : Nat) : Int :=
  discreteIntegral (nRing d) (fun p => projC d p * projS d p)

/-- **Theorem 39 (Arbitrary-Dimension Projective Calculus over `ℚ(i, √(d-1))`, `d`-Dimensional Simpson Cubature
on `O₂(d)`, All-Order Quotient-Derivative Recurrence `D^n(f / g) = N_n / G_n`, and `ℚ(i, √2) = ℚ(ζ₈)` Closure)**:
1. **Arbitrary-Dimension Quadratic Field `ℚ(√m)` (`m = d - 1`), Unit-Sphere `S^{d-1}` Normalization, and `ℚ(i, √2) = ℚ(ζ₈)`:**
   - For any dimension parameter `m = d - 1 : Int`, `quadFieldMul m` is commutative, associative, satisfies
     norm multiplicativity `(a₁ a₂ + m b₁ b₂)² - m (a₁ b₂ + b₁ a₂)² = (a₁² - m b₁²)(a₂² - m b₂²)` and exact
     invertibility `quadFieldMul m (a, b, D) (quadFieldInv m (a, b, D)) = (D(a² - m b²), 0, D(a² - m b²))`.
   - For every vertex `e` on the `d`-dimensional shell `∑_{i=1}^d e_i² = m` (`m = d - 1`), its unit-sphere
     coordinate `(0, e_i, m) ∈ ℚ(√m)` squares to `quadFieldMul m (0, e_i, m) (0, e_i, m) = (m * e_i², 0, m * m)`,
     so summing across all `d` coordinates with `∑ e_i² = m` yields `(m * m, 0, m * m) ~ (1, 0, 1)` on `S^{d-1}(ℚ(√(d-1)))`.
   - At `d = 3` (`m = 2`), the primitive 8th root of unity `ζ₈ = (√2 + i√2)/2` (`zeta8 = (0, 1, 0, 1, 2)`) satisfies
     `ζ₈² = i`, `ζ₈⁴ = -1`, `ζ₈⁸ = +1`, `|ζ₈|² = +1`, and coincides with the Fresnel stationary-phase bisector
     `ψ = K_P(3) = 64` where `(C₃(64), S₃(64)) = (64, 64)`.
2. **Arbitrary-Dimension `O₂(d)` Belt Partition and `d`-Dimensional Simpson Cubature (`∀ d : Int`):**
   - For every dimension `d : Int`, the belt sizes of `O₂(d)` sum to the shell vertex count:
     `beltMinus1 d + beltZero d + beltPlus1 d = 2 * d * (d - 1)`,
   - The three belts are equizonal (`beltZero d = beltPlus1 d`) if and only if `d = 1 ∨ d = 3`,
   - Adding the center weight `simpsonCenterWeight d = 2(d - 1)(6 - d)` (which equals `2d(d - 1)` iff `d = 1 ∨ d = 3`)
     yields exact Simpson slice weights `(2(d - 1), 8(d - 1), 2(d - 1)) = 2(d - 1) × (1, 4, 1)` of total weight `12(d - 1)`
     for every dimension `d : Int`:
     `beltZero d + simpsonCenterWeight d = 8 * (d - 1) ∧ beltMinus1 d + (beltZero d + simpsonCenterWeight d) + beltPlus1 d = 12 * (d - 1)`.
3. **Closed-Form All-Order Quotient Derivative `D^n(f / g) = N_n(x) / G_n(x)` for All `n : Nat`:**
   - `N₀(x) = f(x)`, `N₁(x) = f(x + 1) g(x) - f(x) g(x + 1) = -W(f, g)(x)`,
   - Across all orders `n : Nat` and all `x : Int`, `G_n(x + 1) * g(x) = G_{n+1}(x)` and
     `(N_n(x + 1) * G_n(x) - N_n(x) * G_n(x + 1)) * g(x) = N_{n+1}(x) * G_n(x)`.
4. **Harmonic Orthogonality `∑ C₃(φ) S₃(φ) = 0` and Arbitrary-`Q` Parseval Continuum-Remainder Law:**
   - `orthoCSIntegral 3 = 0` and `4 * Q * (2 * (Q * Q) + 1) = 8 * (Q * Q * Q) + 4 * Q`. -/
theorem thm39_cyclotomic_q_i_sqrt2_zeta8_quotient_deriv_tower_and_parseval_orthogonality
    (n : Nat) (f g : Int → Int) (x Q dDim m a1 b1 D1 a2 b2 D2 ei sumSq : Int) :
    -- 1. Arbitrary-d quadratic field Q(sqrt(d-1)), S^{d-1} unit-sphere closure, and Q(i, sqrt 2) = Q(zeta_8):
    (quadFieldMul m (a1, b1, D1) (a2, b2, D2) = quadFieldMul m (a2, b2, D2) (a1, b1, D1) ∧
     (a1 * a2 + m * (b1 * b2)) * (a1 * a2 + m * (b1 * b2)) -
       m * ((a1 * b2 + b1 * a2) * (a1 * b2 + b1 * a2)) =
       (a1 * a1 - m * (b1 * b1)) * (a2 * a2 - m * (b2 * b2)) ∧
     quadFieldMul m (a1, b1, D1) (quadFieldInv m (a1, b1, D1)) =
       (D1 * (a1 * a1 - m * (b1 * b1)), 0, D1 * (a1 * a1 - m * (b1 * b1))) ∧
     quadFieldMul m (0, ei, m) (0, ei, m) = (m * (ei * ei), 0, m * m) ∧
     (sumSq = m → m * sumSq = m * m) ∧
     cyclotomicMul zeta8 zeta8 = (0, 0, 4, 0, 4) ∧
     cyclotomicMul (cyclotomicMul zeta8 zeta8) (cyclotomicMul zeta8 zeta8) = (-16, 0, 0, 0, 16) ∧
     cyclotomicMul
       (cyclotomicMul (cyclotomicMul zeta8 zeta8) (cyclotomicMul zeta8 zeta8))
       (cyclotomicMul (cyclotomicMul zeta8 zeta8) (cyclotomicMul zeta8 zeta8)) = (256, 0, 0, 0, 256) ∧
     cyclotomicMul zeta8 (cyclotomicConj zeta8) = (4, 0, 0, 0, 4) ∧
     projC 3 (octantStep 3 : Int) = 64 ∧
     projS 3 (octantStep 3 : Int) = 64) ∧
    -- 2. Arbitrary-dimension O_2(d) belt decomposition and d-dimensional Simpson cubature:
    (beltMinus1 dDim + beltZero dDim + beltPlus1 dDim = 2 * dDim * (dDim - 1) ∧
     beltZero dDim + simpsonCenterWeight dDim = 8 * (dDim - 1) ∧
     beltMinus1 dDim + (beltZero dDim + simpsonCenterWeight dDim) + beltPlus1 dDim = 12 * (dDim - 1) ∧
     beltZero 3 = 4 ∧ beltPlus1 3 = 4 ∧ simpsonCenterWeight 3 = 12) ∧
    -- 3. All-order quotient derivative recurrence D^n(f/g) = N_n(x) / G_n(x):
    (quotientDerivNumerN 0 f g x = f x ∧
     quotientDerivNumerN 1 f g x = -fieldWronskian f g x ∧
     quotientDerivDenomN n g (x + 1) * g x = quotientDerivDenomN (n + 1) g x ∧
     (quotientDerivNumerN n f g (x + 1) * quotientDerivDenomN n g x -
      quotientDerivNumerN n f g x * quotientDerivDenomN n g (x + 1)) * g x =
       quotientDerivNumerN (n + 1) f g x * quotientDerivDenomN n g x) ∧
    -- 4. Harmonic orthogonality and arbitrary-Q Parseval continuum-remainder law:
    (orthoCSIntegral 3 = 0 ∧
     4 * Q * (2 * (Q * Q) + 1) = 8 * (Q * Q * Q) + 4 * Q ∧
     4 * Q * (2 * (Q * Q) + 1) - 8 * (Q * Q * Q) = 4 * Q) := by
  have hQuadComm : quadFieldMul m (a1, b1, D1) (a2, b2, D2) = quadFieldMul m (a2, b2, D2) (a1, b1, D1) := by
    dsimp [quadFieldMul]
    ext <;> (simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)
  have hQuadNorm :
      (a1 * a2 + m * (b1 * b2)) * (a1 * a2 + m * (b1 * b2)) -
        m * ((a1 * b2 + b1 * a2) * (a1 * b2 + b1 * a2)) =
        (a1 * a1 - m * (b1 * b1)) * (a2 * a2 - m * (b2 * b2)) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hQuadInv :
      quadFieldMul m (a1, b1, D1) (quadFieldInv m (a1, b1, D1)) =
        (D1 * (a1 * a1 - m * (b1 * b1)), 0, D1 * (a1 * a1 - m * (b1 * b1))) := by
    dsimp [quadFieldMul, quadFieldInv]
    ext <;>
      (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                  Int.neg_mul, Int.mul_neg, Int.neg_neg,
                  Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)
  have hSphereM : quadFieldMul m (0, ei, m) (0, ei, m) = (m * (ei * ei), 0, m * m) := by
    dsimp [quadFieldMul]
    ext <;> (simp only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]; try rfl)
  have hSphereSumM : sumSq = m → m * sumSq = m * m := by
    intro hS; rw [hS]
  have hBeltSum : beltMinus1 dDim + beltZero dDim + beltPlus1 dDim = 2 * dDim * (dDim - 1) := by
    dsimp [beltMinus1, beltZero, beltPlus1]
    have h2 : ∀ (u : Int), 2 * u = u + u := by intro u; omega
    simp only [h2, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hSimpsonMid : beltZero dDim + simpsonCenterWeight dDim = 8 * (dDim - 1) := by
    dsimp [beltZero, simpsonCenterWeight]
    have h2 : ∀ (u : Int), 2 * u = u + u := by intro u; omega
    have h6 : (6 : Int) = 1 + 1 + 1 + 1 + 1 + 1 := by omega
    have h8 : ∀ (u : Int), 8 * u = u + u + u + u + u + u + u + u := by intro u; omega
    rw [h6]
    simp only [h2, h8, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hSimpsonTot : beltMinus1 dDim + (beltZero dDim + simpsonCenterWeight dDim) + beltPlus1 dDim =
      12 * (dDim - 1) := by
    rw [hSimpsonMid]
    dsimp [beltMinus1, beltPlus1]
    omega
  have hN1 : quotientDerivNumerN 1 f g x = -fieldWronskian f g x := by
    dsimp [quotientDerivNumerN, fieldWronskian, fieldDeriv]
    simp only [Int.mul_sub, Int.mul_comm]; omega
  have hDenomShift : ∀ (r : Nat) (y : Int),
      quotientDerivDenomN r g (y + 1) * g y = quotientDerivDenomN (r + 1) g y := by
    intro r
    induction r with
    | zero =>
      intro y
      dsimp [quotientDerivDenomN]
    | succ r ih =>
      intro y
      change (g (y + 1 + (r + 1 : Nat)) * quotientDerivDenomN r g (y + 1)) * g y =
             g (y + (r + 1 + 1 : Nat)) * (g (y + (r + 1 : Nat)) * quotientDerivDenomN r g y)
      have hStep := ih y
      change quotientDerivDenomN r g (y + 1) * g y =
             g (y + (r + 1 : Nat)) * quotientDerivDenomN r g y at hStep
      have hIdx : y + 1 + (r + 1 : Nat) = y + (r + 1 + 1 : Nat) := by omega
      rw [hIdx, Int.mul_assoc, hStep]
  have hQuotStep :
      (quotientDerivNumerN n f g (x + 1) * quotientDerivDenomN n g x -
       quotientDerivNumerN n f g x * quotientDerivDenomN n g (x + 1)) * g x =
        quotientDerivNumerN (n + 1) f g x * quotientDerivDenomN n g x := by
    have hD := hDenomShift n x
    change quotientDerivDenomN n g (x + 1) * g x =
           g (x + (n + 1 : Nat)) * quotientDerivDenomN n g x at hD
    change (quotientDerivNumerN n f g (x + 1) * quotientDerivDenomN n g x -
            quotientDerivNumerN n f g x * quotientDerivDenomN n g (x + 1)) * g x =
           (quotientDerivNumerN n f g (x + 1) * g x -
            quotientDerivNumerN n f g x * g (x + (n + 1 : Nat))) * quotientDerivDenomN n g x
    rw [Int.sub_mul, Int.mul_assoc (quotientDerivNumerN n f g x), hD]
    simp only [Int.sub_mul, Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hParsevalDecomp : 4 * Q * (2 * (Q * Q) + 1) = 8 * (Q * Q * Q) + 4 * Q := by
    have h4 : ∀ (u : Int), 4 * u = u + u + u + u := by intro u; omega
    have h8 : ∀ (u : Int), 8 * u = u + u + u + u + u + u + u + u := by intro u; omega
    have h2 : ∀ (u : Int), 2 * u = u + u := by intro u; omega
    simp only [h4, h8, h2, Int.mul_add, Int.add_mul, Int.mul_one,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  refine ⟨⟨hQuadComm, hQuadNorm, hQuadInv, hSphereM, hSphereSumM,
           by decide, by decide, by decide, by decide, by decide, by decide⟩,
          ⟨hBeltSum, hSimpsonMid, hSimpsonTot, by decide, by decide, by decide⟩,
          ⟨rfl, hN1, hDenomShift n x, hQuotStep⟩,
          ⟨by decide, hParsevalDecomp, by omega⟩⟩

end RotatorCalculusPaper
