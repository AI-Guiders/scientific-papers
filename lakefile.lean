import Lake
open Lake DSL

package «cuboctahedral-rotator-calculus» where
  version := v!"1.0.0"

@[default_target]
lean_lib «RotatorCalculusPaper» where
  roots := #[
    `AxiomGuard,
    `RotatorQuadrature,
    `ProjectiveFieldCalculus,
    `InverseTrigHyperbolic,
    `LogicCohomology,
    `PillaiDiophantine,
    `AbcPlanetaryWronskian,
    `ModelTheoreticLimit,
    `CollatzPlanetarySplice,
    `CollatzGearMonoid,
    `RiemannHolonomy,
    `MinkowskiCounterwaveCascade,
    `RotatorCalculusPaper
  ]
