# State and kinematics ownership (#36)

Decision: keep the existing orthogonal primitives; do not add a Cartesian-state
wrapper or a time-dependent transformation type in this release.

`keplerian::state::CartesianState` already stores affn Position and Velocity,
with public fields and kilometre defaults. `principia::DynamicsState` adds a
continuous-scale epoch and public fields. Siderust `TemeState` has private fields,
astronomical coordinate wrappers and a UTC epoch. Their shared part is storage,
not duplicated geometry algorithms. Moving it would require compatibility wrappers
or change public fields, constructors, center-parameter bounds or Serde schemas.
The existing Position retains C::Params; Velocity carries a frame and quantity
unit. A new aggregate would remove none of that maintained logic. Keep epochs
and propagation out of affn. Reconsider only with a real common operation/caller.

`Rotation3` rotates free vectors; it does not convert coordinate derivatives.
For the same origin, with externally supplied R(t),

    r_B = R r_A
    v_B = R v_A + Rdot r_A

Rdot has inverse-time units. Its output must be converted into the velocity unit
before addition. For moving origins, additionally subtract the origin displacement
and velocity, using a consistently defined frame and derivative convention.
Earth orientation, UT1/EOP and TEME conventions belong to Siderust.

The derivative under inverse and composition obeys

    Q = R^-1, Qdot = -Q Rdot Q
    T = S R, Tdot = Sdot R + S Rdot

`BlockDiagRotation6` continues to mean diag(R,R). Covariances of rotating-frame
coordinate states instead require J P J^T with J=[R,0;Rdot,R]. A fixed evaluation
epoch does not make Rdot vanish. No production caller currently supplies a full
rotation derivative for this transformation; adding an unused public kinematics
framework would increase independently maintained API surface. Independent analytic
and finite-difference tests document the limitation without promising an astronomy
state conversion. Position/Velocity, existing frame typing, optional Serde and
core-only support remain unchanged. Production algorithm count is unchanged.
