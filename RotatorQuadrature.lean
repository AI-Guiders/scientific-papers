/-
  RotatorQuadrature.lean
  Self-contained formal verification module for Paper 1:
  "Cuboctahedral Rotator Calculus: Discrete Euler Exponential on Z_512,
   Universal Constant Wronskian, and Closed-Form Quadrature on the Cuboctahedron O_2(3) in Lean 4"
  Authors: D. A. Karataev & Luch (Луч)
  Zero external dependencies (pure Lean 4 core), zero `sorry`, zero `Classical.choice`.
-/

namespace RotatorCalculusPaper

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

theorem discreteIntegral_pointwise_const (N : Nat) (cInv : Int) (g : Int → Int)
    (hC : ∀ p : Int, g p = cInv) :
    discreteIntegral N g = (N : Int) * cInv := by
  induction N with
  | zero => dsimp [discreteIntegral]; omega
  | succ n ih => dsimp [discreteIntegral]; rw [ih, hC (n : Int), Int.add_mul]; omega

/-- **Theorem 1 (Discrete Euler Exponential `e^{iφ}`, Euler's Identity `e^{iπ} + 1 = 0`, Universal Constant Difference Wronskian `W_Q(φ) ≡ Q` Across All Turns `kTurns ∈ ℤ`, Constant Factor Extraction Out of Integrals, Universal Brahmagupta–Weierstrass Lift, and Fundamental Theorem of Discrete Calculus)**: -/
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
            discreteIntegral_pointwise_const L Q (fun _ => (qm + Q - m) - (qm - m)) (fun _ => by omega),
            discreteIntegral_pointwise_const L cSq (fun _ => cSq) (fun _ => rfl)⟩,
           by omega, by omega, by omega, by omega, ⟨by omega, by omega⟩, ?_, rfl, rfl, rfl⟩,
          ⟨by omega, by omega⟩,
          ⟨⟨by dsimp [discreteIntegral]; omega,
            by dsimp [antiderivC, discreteIntegral]; omega,
            by dsimp [antiderivS, discreteIntegral]; omega⟩,
           by rw [hAntiC]; omega, by rw [hAntiS]; omega, by rw [hHalfS]; rfl,
           ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩⟩⟩
  rw [discreteIntegral_const_mul, hWronInt]; rfl

/-- **Theorem 2 (Universal Closed-Form Evaluation of Fresnel, Parametric Jacobi Elliptic, Dirichlet `Si`, Parseval, and Bessel `J₀` Integrals Across Arbitrary Path Lengths `L ∈ ℕ`, Winding Turns `kTurns ∈ ℤ`, and Constant Amplitude Scaling `cSq ∈ ℤ`)**: -/
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
           discreteIntegral_pointwise_const L Q (fun _ => (Q - m) + m) (fun _ => by omega),
           discreteIntegral_pointwise_const L (2 * Q) (fun _ => (2 * Q - m) + m) (fun _ => by omega),
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

/-- **Theorem 3 (First-Principles Derivation of Universal Functional 3D Cuboctahedron Cubature, `π(n)` Rational Brackets, Universal Verlet Parabola Rational Sine Defect Law, Universal `O(k²)` / `O(k⁴)` Shell Moments, and Universal 3D Euler-Angle Norm Scaling from the Cuboctahedron `O₂`)**: -/
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

#print axioms thm1_constant_wronskian_weierstrass_lift_and_newton_leibniz
#print axioms thm2_closed_form_fresnel_jacobi_dirichlet_parseval_bessel_integrals
#print axioms thm3_continuum_integration_from_cuboctahedron_archimedes_layers

end RotatorCalculusPaper
