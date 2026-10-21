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
The formulas below use the convention that `R(t)` maps components expressed
in source frame A to components expressed in destination frame B. A dot is a
derivative with respect to the same physical time coordinate in both frames,
and every displacement/velocity is expressed in the frame named by its
subscript. For the same origin, with externally supplied R(t),

    r_B = R r_A
    v_B = R v_A + Rdot r_A

Rdot has inverse-time units. Its output must be converted into the velocity unit
before addition. For a moving destination origin, let `d_A(t)` be the
displacement from the source origin to the destination origin, expressed in A.
Let `d_dot_A` be its time derivative, also expressed in A. Then

    r_B = R (r_A - d_A)

    v_B = R (v_A - d_dot_A) + Rdot (r_A - d_A)

Thus `d_A` has length units, `d_dot_A` and `v_A` have length/time units, and
`Rdot` has inverse-time units. Both terms in the velocity equation therefore
have length/time units. A simple vector rotation is sufficient for a free
velocity vector, but not for the derivative of coordinates in a moving or
rotating frame. Earth orientation, UT1/EOP and TEME conventions belong to
Siderust.

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
