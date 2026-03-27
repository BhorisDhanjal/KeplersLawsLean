import Kepler.Dynamics
import Mathlib.Algebra.Lie.Classical
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.style.multiGoal false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.style.setOption false

namespace Kepler

noncomputable section

def basisVec (i : Fin 3) : Vec3 := EuclideanSpace.single i (1 : Real)

def partialQ (F : PhaseSpace -> Real) (i : Fin 3) (z : PhaseSpace) : Real := 
  deriv (fun s : Real => F (z.1 + s • basisVec i, z.2)) 0

def partialP (F : PhaseSpace -> Real) (i : Fin 3) (z : PhaseSpace) : Real := 
  deriv (fun s : Real => F (z.1, z.2 + s • basisVec i)) 0

def poissonBracket (F G : PhaseSpace -> Real) : PhaseSpace -> Real := 
  fun z =>
    (partialQ F 0 z * partialP G 0 z - partialP F 0 z * partialQ G 0 z) +
    (partialQ F 1 z * partialP G 1 z - partialP F 1 z * partialQ G 1 z) +
    (partialQ F 2 z * partialP G 2 z - partialP F 2 z * partialQ G 2 z)

def keplerHamiltonian (mp : MassParam) (gp : GravitationalParam) : PhaseSpace -> Real := energy mp gp

def L0 (z : PhaseSpace) : Real := z.1 1 * z.2 2 - z.1 2 * z.2 1
def L1 (z : PhaseSpace) : Real := z.1 2 * z.2 0 - z.1 0 * z.2 2
def L2 (z : PhaseSpace) : Real := z.1 0 * z.2 1 - z.1 1 * z.2 0

def F0 (z : PhaseSpace) : Real := z.2 1 * L2 z - z.2 2 * L1 z
def F1 (z : PhaseSpace) : Real := z.2 2 * L0 z - z.2 0 * L2 z
def F2 (z : PhaseSpace) : Real := z.2 0 * L1 z - z.2 1 * L0 z

def U0 (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace) : Real :=
  ((mp.m * gp.mu) / radialDist z.1) * z.1 0
def U1 (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace) : Real :=
  ((mp.m * gp.mu) / radialDist z.1) * z.1 1
def U2 (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace) : Real :=
  ((mp.m * gp.mu) / radialDist z.1) * z.1 2

def A0 (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace) : Real := F0 z - U0 mp gp z
def A1 (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace) : Real := F1 z - U1 mp gp z
def A2 (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace) : Real := F2 z - U2 mp gp z

def comomentMap (u : Vec3) : PhaseSpace -> Real := 
  fun z => inner ℝ u (angularMomentum z)

def L_u (u : Vec3) : PhaseSpace -> Real := 
  fun z => (u 0) * L0 z + (u 1) * L1 z + (u 2) * L2 z

def A_u (mp : MassParam) (gp : GravitationalParam) (u : Vec3) : PhaseSpace -> Real :=
  fun z => (u 0) * A0 mp gp z + (u 1) * A1 mp gp z + (u 2) * A2 mp gp z

lemma F0_eq_cross (z : PhaseSpace) : F0 z = cross z.2 (angularMomentum z) 0 := by
  simp [F0, angularMomentum, L1, L2, cross, cross_apply]

lemma F1_eq_cross (z : PhaseSpace) : F1 z = cross z.2 (angularMomentum z) 1 := by
  simp [F1, angularMomentum, L0, L2, cross, cross_apply]

lemma F2_eq_cross (z : PhaseSpace) : F2 z = cross z.2 (angularMomentum z) 2 := by
  simp [F2, angularMomentum, L0, L1, cross, cross_apply]

lemma A0_eq_laplaceLenz (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace) :
    A0 mp gp z = laplaceLenz mp gp z 0 := by
  simp [A0, U0, laplaceLenz, F0_eq_cross, angularMomentum, radialDist]

lemma A1_eq_laplaceLenz (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace) :
    A1 mp gp z = laplaceLenz mp gp z 1 := by
  simp [A1, U1, laplaceLenz, F1_eq_cross, angularMomentum, radialDist]

lemma A2_eq_laplaceLenz (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace) :
    A2 mp gp z = laplaceLenz mp gp z 2 := by
  simp [A2, U2, laplaceLenz, F2_eq_cross, angularMomentum, radialDist]

lemma L_u_eq_comomentMap (u : Vec3) : L_u u = comomentMap u := by
  funext z
  simp [L_u, comomentMap, inner_fin3, angularMomentum, L0, L1, L2, cross, cross_apply]

lemma deriv_const_add_mul_zero (c a : Real) : deriv (fun s : Real => c + s * a) 0 = a := by
  have h : HasDerivAt (fun s : Real => c + s * a) a 0 := by
    simpa [one_mul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using ((hasDerivAt_id (0 : Real)).mul_const a).const_add c
  simpa using h.deriv

lemma deriv_const_add_mul_add_sq_zero (c a b : Real) :
    deriv (fun s : Real => c + s * a + s ^ (2 : Nat) * b) 0 = a := by
  have hconst : HasDerivAt (fun s : Real => c) 0 0 := by
    simpa using (hasDerivAt_const (0 : Real) c)
  have hid : HasDerivAt (fun s : Real => s) 1 0 := hasDerivAt_id 0
  have hlin : HasDerivAt (fun s : Real => s * a) a 0 := by
    simpa [one_mul] using hid.mul_const a
  have hsq : HasDerivAt (fun s : Real => s ^ (2 : Nat)) 0 0 := by
    simpa [pow_two] using hid.mul hid
  have hsqb : HasDerivAt (fun s : Real => s ^ (2 : Nat) * b) 0 0 := by
    simpa using hsq.mul_const b
  have hsum : HasDerivAt (fun s : Real => c + s * a + s ^ (2 : Nat) * b) a 0 := by
    have h1 : HasDerivAt (fun s : Real => c + s * a) a 0 := by
      convert (hconst.add hlin) using 1 <;> ring
    have h2 : HasDerivAt (fun s : Real => c + s * a + s ^ (2 : Nat) * b) (a + 0) 0 := by
      convert (h1.add hsqb) using 1 <;> ring
    simpa [add_zero] using h2
  simpa using hsum.deriv

lemma hasDerivAt_const_add_mul_zero (c a : Real) :
    HasDerivAt (fun s : Real => c + s * a) a 0 := by
  simpa [one_mul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    using ((hasDerivAt_id (0 : Real)).mul_const a).const_add c

lemma hasDerivAt_const_add_mul_add_sq_zero (c a b : Real) :
    HasDerivAt (fun s : Real => c + s * a + s ^ (2 : Nat) * b) a 0 := by
  have hconst : HasDerivAt (fun s : Real => c) 0 0 := by
    simpa using (hasDerivAt_const (0 : Real) c)
  have hid : HasDerivAt (fun s : Real => s) 1 0 := hasDerivAt_id 0
  have hlin : HasDerivAt (fun s : Real => s * a) a 0 := by
    simpa [one_mul] using hid.mul_const a
  have hsq : HasDerivAt (fun s : Real => s ^ (2 : Nat)) 0 0 := by
    simpa [pow_two] using hid.mul hid
  have hsqb : HasDerivAt (fun s : Real => s ^ (2 : Nat) * b) 0 0 := by
    simpa using hsq.mul_const b
  have hsum : HasDerivAt (fun s : Real => c + s * a + s ^ (2 : Nat) * b) a 0 := by
    have h1 : HasDerivAt (fun s : Real => c + s * a) a 0 := by
      convert (hconst.add hlin) using 1 <;> ring
    have h2 : HasDerivAt (fun s : Real => c + s * a + s ^ (2 : Nat) * b) (a + 0) 0 := by
      convert (h1.add hsqb) using 1 <;> ring
    simpa [add_zero] using h2
  simpa using hsum

def X_u (u : Vec3) : PhaseSpace -> Real :=
  fun z => u 0 * z.1 0 + u 1 * z.1 1 + u 2 * z.1 2

def P_u (u : Vec3) : PhaseSpace -> Real :=
  fun z => u 0 * z.2 0 + u 1 * z.2 1 + u 2 * z.2 2

lemma X_u_eq_inner (u : Vec3) : X_u u = fun z : PhaseSpace => inner ℝ u z.1 := by
  funext z
  rw [inner_fin3]
  simp [X_u]

lemma P_u_eq_inner (u : Vec3) : P_u u = fun z : PhaseSpace => inner ℝ u z.2 := by
  funext z
  rw [inner_fin3]
  simp [P_u]

lemma partialQ_position_coord (i k : Fin 3) (z : PhaseSpace) :
    partialQ (fun z : PhaseSpace => z.1 i) k z = if i = k then 1 else 0 := by
  unfold partialQ
  by_cases hik : i = k
  · subst hik
    simpa [basisVec, one_mul] using (deriv_const_add_mul_zero (z.1 i) (1 : Real))
  · simpa [basisVec, hik] using (deriv_const (z.1 i))

lemma partialP_position_coord (i k : Fin 3) (z : PhaseSpace) :
    partialP (fun z : PhaseSpace => z.1 i) k z = 0 := by
  unfold partialP
  simpa using deriv_const (z.1 i)

lemma partialQ_momentum_coord (i k : Fin 3) (z : PhaseSpace) :
    partialQ (fun z : PhaseSpace => z.2 i) k z = 0 := by
  unfold partialQ
  simpa using deriv_const (z.2 i)

lemma partialP_momentum_coord (i k : Fin 3) (z : PhaseSpace) :
    partialP (fun z : PhaseSpace => z.2 i) k z = if i = k then 1 else 0 := by
  unfold partialP
  by_cases hik : i = k
  · subst hik
    simpa [basisVec, one_mul] using (deriv_const_add_mul_zero (z.2 i) (1 : Real))
  · simpa [basisVec, hik] using (deriv_const (z.2 i))

lemma basic_canonical_brackets (i j : Fin 3) :
    poissonBracket (fun z : PhaseSpace => z.1 i) (fun z => z.1 j) = 0 ∧
    poissonBracket (fun z : PhaseSpace => z.2 i) (fun z => z.2 j) = 0 ∧
    poissonBracket (fun z : PhaseSpace => z.1 i) (fun z => z.2 j) =
      fun _ => if i = j then 1 else 0 := by
  constructor
  · funext z
    simp [poissonBracket, partialQ_position_coord, partialP_position_coord]
  constructor
  · funext z
    simp [poissonBracket, partialQ_momentum_coord, partialP_momentum_coord]
  · funext z
    fin_cases i <;> fin_cases j <;>
      simp [poissonBracket, partialQ_position_coord, partialP_position_coord,
        partialQ_momentum_coord, partialP_momentum_coord]

lemma partialQ_X_u (u : Vec3) (k : Fin 3) (z : PhaseSpace) :
    partialQ (X_u u) k z = u k := by
  fin_cases k
  · unfold partialQ X_u
    have h : deriv (fun s : Real => z.1 0 + s) 0 = 1 := by
      simpa [one_mul] using (deriv_const_add_mul_zero (z.1 0) (1 : Real))
    simp [basisVec, h]
  · unfold partialQ X_u
    have h : deriv (fun s : Real => z.1 1 + s) 0 = 1 := by
      simpa [one_mul] using (deriv_const_add_mul_zero (z.1 1) (1 : Real))
    simp [basisVec, h]
  · unfold partialQ X_u
    have h : deriv (fun s : Real => z.1 2 + s) 0 = 1 := by
      simpa [one_mul] using (deriv_const_add_mul_zero (z.1 2) (1 : Real))
    simp [basisVec, h]

lemma partialP_X_u (u : Vec3) (k : Fin 3) (z : PhaseSpace) :
    partialP (X_u u) k z = 0 := by
  unfold partialP X_u
  simp

lemma partialQ_P_u (u : Vec3) (k : Fin 3) (z : PhaseSpace) :
    partialQ (P_u u) k z = 0 := by
  unfold partialQ P_u
  simp

lemma partialP_P_u (u : Vec3) (k : Fin 3) (z : PhaseSpace) :
    partialP (P_u u) k z = u k := by
  fin_cases k
  · unfold partialP P_u
    have h : deriv (fun s : Real => z.2 0 + s) 0 = 1 := by
      simpa [one_mul] using (deriv_const_add_mul_zero (z.2 0) (1 : Real))
    simp [basisVec, h]
  · unfold partialP P_u
    have h : deriv (fun s : Real => z.2 1 + s) 0 = 1 := by
      simpa [one_mul] using (deriv_const_add_mul_zero (z.2 1) (1 : Real))
    simp [basisVec, h]
  · unfold partialP P_u
    have h : deriv (fun s : Real => z.2 2 + s) 0 = 1 := by
      simpa [one_mul] using (deriv_const_add_mul_zero (z.2 2) (1 : Real))
    simp [basisVec, h]

lemma poisson_X_u_X_v (u v : Vec3) :
    poissonBracket (X_u u) (X_u v) = 0 := by
  funext z
  simp [poissonBracket, partialQ_X_u, partialP_X_u]

lemma poisson_P_u_P_v (u v : Vec3) :
    poissonBracket (P_u u) (P_u v) = 0 := by
  funext z
  simp [poissonBracket, partialQ_P_u, partialP_P_u]

lemma poisson_X_u_P_v (u v : Vec3) :
    poissonBracket (X_u u) (P_u v) = fun _ => inner ℝ u v := by
  funext z
  rw [inner_fin3]
  simp [poissonBracket, partialQ_X_u, partialP_X_u, partialQ_P_u, partialP_P_u]

set_option linter.flexible false in
lemma partialQ_L_u_0 (u : Vec3) (z : PhaseSpace) :
    partialQ (L_u u) 0 z = -(u 1) * z.2 2 + (u 2) * z.2 1 := by
  unfold partialQ L_u
  simp [L0, L1, L2, basisVec]
  have hfun :
      (fun s : Real =>
        u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
          u 1 * (z.1 2 * z.2 0 - (z.1 0 + s) * z.2 2) +
          u 2 * ((z.1 0 + s) * z.2 1 - z.1 1 * z.2 0))
        =
      fun s : Real =>
        (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
          u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
          u 2 * (z.1 0 * z.2 1 - z.1 1 * z.2 0)) +
        s * (-(u 1) * z.2 2 + (u 2) * z.2 1) := by
    funext s
    ring
  rw [hfun]
  simpa using
    (deriv_const_add_mul_zero
      (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
        u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
        u 2 * (z.1 0 * z.2 1 - z.1 1 * z.2 0))
      (-(u 1) * z.2 2 + (u 2) * z.2 1))

set_option linter.flexible false in
lemma partialQ_L_u_1 (u : Vec3) (z : PhaseSpace) :
    partialQ (L_u u) 1 z = -(u 2) * z.2 0 + (u 0) * z.2 2 := by
  unfold partialQ L_u
  simp [L0, L1, L2, basisVec]
  have hfun :
      (fun s : Real =>
        u 0 * ((z.1 1 + s) * z.2 2 - z.1 2 * z.2 1) +
          u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
          u 2 * (z.1 0 * z.2 1 - (z.1 1 + s) * z.2 0))
        =
      fun s : Real =>
        (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
          u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
          u 2 * (z.1 0 * z.2 1 - z.1 1 * z.2 0)) +
        s * (-(u 2) * z.2 0 + (u 0) * z.2 2) := by
    funext s
    ring
  rw [hfun]
  simpa using
    (deriv_const_add_mul_zero
      (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
        u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
        u 2 * (z.1 0 * z.2 1 - z.1 1 * z.2 0))
      (-(u 2) * z.2 0 + (u 0) * z.2 2))

set_option linter.flexible false in
lemma partialQ_L_u_2 (u : Vec3) (z : PhaseSpace) :
    partialQ (L_u u) 2 z = -(u 0) * z.2 1 + (u 1) * z.2 0 := by
  unfold partialQ L_u
  simp [L0, L1, L2, basisVec]
  have hfun :
      (fun s : Real =>
        u 0 * (z.1 1 * z.2 2 - (z.1 2 + s) * z.2 1) +
          u 1 * ((z.1 2 + s) * z.2 0 - z.1 0 * z.2 2))
        =
      fun s : Real =>
        (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
          u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2)) +
        s * (-(u 0) * z.2 1 + (u 1) * z.2 0) := by
    funext s
    ring
  rw [hfun]
  simpa using
    (deriv_const_add_mul_zero
      (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
        u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2))
      (-(u 0) * z.2 1 + (u 1) * z.2 0))

set_option linter.flexible false in
lemma partialP_L_u_0 (u : Vec3) (z : PhaseSpace) :
    partialP (L_u u) 0 z = (u 1) * z.1 2 - (u 2) * z.1 1 := by
  unfold partialP L_u
  simp [L0, L1, L2, basisVec]
  have hfun :
      (fun s : Real =>
        u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
          u 1 * (z.1 2 * (z.2 0 + s) - z.1 0 * z.2 2) +
          u 2 * (z.1 0 * z.2 1 - z.1 1 * (z.2 0 + s)))
        =
      fun s : Real =>
        (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
          u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
          u 2 * (z.1 0 * z.2 1 - z.1 1 * z.2 0)) +
        s * ((u 1) * z.1 2 - (u 2) * z.1 1) := by
    funext s
    ring
  rw [hfun]
  simpa using
    (deriv_const_add_mul_zero
      (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
        u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
        u 2 * (z.1 0 * z.2 1 - z.1 1 * z.2 0))
      ((u 1) * z.1 2 - (u 2) * z.1 1))

set_option linter.flexible false in
lemma partialP_L_u_1 (u : Vec3) (z : PhaseSpace) :
    partialP (L_u u) 1 z = (u 2) * z.1 0 - (u 0) * z.1 2 := by
  unfold partialP L_u
  simp [L0, L1, L2, basisVec]
  have hfun :
      (fun s : Real =>
        u 0 * (z.1 1 * z.2 2 - z.1 2 * (z.2 1 + s)) +
          u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
          u 2 * (z.1 0 * (z.2 1 + s) - z.1 1 * z.2 0))
        =
      fun s : Real =>
        (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
          u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
          u 2 * (z.1 0 * z.2 1 - z.1 1 * z.2 0)) +
        s * ((u 2) * z.1 0 - (u 0) * z.1 2) := by
    funext s
    ring
  rw [hfun]
  simpa using
    (deriv_const_add_mul_zero
      (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
        u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
        u 2 * (z.1 0 * z.2 1 - z.1 1 * z.2 0))
      ((u 2) * z.1 0 - (u 0) * z.1 2))

set_option linter.flexible false in
lemma partialP_L_u_2 (u : Vec3) (z : PhaseSpace) :
    partialP (L_u u) 2 z = (u 0) * z.1 1 - (u 1) * z.1 0 := by
  unfold partialP L_u
  simp [L0, L1, L2, basisVec]
  have hfun :
      (fun s : Real =>
        u 0 * (z.1 1 * (z.2 2 + s) - z.1 2 * z.2 1) +
          u 1 * (z.1 2 * z.2 0 - z.1 0 * (z.2 2 + s)))
        =
      fun s : Real =>
        (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
          u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2)) +
        s * ((u 0) * z.1 1 - (u 1) * z.1 0) := by
    funext s
    ring
  rw [hfun]
  simpa using
    (deriv_const_add_mul_zero
      (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
        u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2))
      ((u 0) * z.1 1 - (u 1) * z.1 0))

lemma poisson_X_v_L_u_and_P_v_L_u (u v : Vec3) :
    poissonBracket (X_u v) (L_u u) = X_u (cross v u) ∧
    poissonBracket (P_u v) (L_u u) = P_u (cross v u) := by
  constructor
  · funext z
    unfold poissonBracket
    simp [partialQ_X_u, partialP_X_u, partialP_L_u_0, partialP_L_u_1, partialP_L_u_2,
      X_u, cross, cross_apply]
    ring_nf
  · funext z
    unfold poissonBracket
    simp [partialQ_P_u, partialP_P_u, partialQ_L_u_0, partialQ_L_u_1, partialQ_L_u_2,
      P_u, cross, cross_apply]
    ring_nf

lemma partialP_keplerHamiltonian (mp : MassParam) (gp : GravitationalParam) (i : Fin 3)
    (z : PhaseSpace) :
    partialP (keplerHamiltonian mp gp) i z = z.2 i / mp.m := by
  fin_cases i
  · unfold partialP keplerHamiltonian energy
    change deriv
        (fun s : Real => (1 / (2 * mp.m)) * ‖z.2 + s • basisVec 0‖ ^ (2 : Nat) - gp.mu / ‖z.1‖)
        0 =
      z.2 0 / mp.m
    have hfun :
        (fun s : Real => (1 / (2 * mp.m)) * ‖z.2 + s • basisVec 0‖ ^ (2 : Nat) - gp.mu / ‖z.1‖) =
        fun s : Real =>
          ((1 / (2 * mp.m)) * ‖z.2‖ ^ (2 : Nat) - gp.mu / ‖z.1‖) +
            s * (z.2 0 / mp.m) + s ^ (2 : Nat) * (1 / (2 * mp.m)) := by
      funext s
      have hsq1 :
          ‖z.2 + s • basisVec 0‖ ^ (2 : Nat) =
            (z.2 0 + s) ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
        simpa [basisVec, Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) (z.2 + s • basisVec 0))
      have hsq2 :
          ‖z.2‖ ^ (2 : Nat) = z.2 0 ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
        simpa [Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.2)
      rw [hsq1, hsq2]
      ring
    rw [hfun]
    simpa using
      (deriv_const_add_mul_add_sq_zero
        ((1 / (2 * mp.m)) * ‖z.2‖ ^ (2 : Nat) - gp.mu / ‖z.1‖)
        (z.2 0 / mp.m) (1 / (2 * mp.m)))
  · unfold partialP keplerHamiltonian energy
    change deriv
        (fun s : Real => (1 / (2 * mp.m)) * ‖z.2 + s • basisVec 1‖ ^ (2 : Nat) - gp.mu / ‖z.1‖)
        0 =
      z.2 1 / mp.m
    have hfun :
        (fun s : Real => (1 / (2 * mp.m)) * ‖z.2 + s • basisVec 1‖ ^ (2 : Nat) - gp.mu / ‖z.1‖) =
        fun s : Real =>
          ((1 / (2 * mp.m)) * ‖z.2‖ ^ (2 : Nat) - gp.mu / ‖z.1‖) +
            s * (z.2 1 / mp.m) + s ^ (2 : Nat) * (1 / (2 * mp.m)) := by
      funext s
      have hsq1 :
          ‖z.2 + s • basisVec 1‖ ^ (2 : Nat) =
            z.2 0 ^ (2 : Nat) + (z.2 1 + s) ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
        simpa [basisVec, Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) (z.2 + s • basisVec 1))
      have hsq2 :
          ‖z.2‖ ^ (2 : Nat) = z.2 0 ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
        simpa [Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.2)
      rw [hsq1, hsq2]
      ring
    rw [hfun]
    simpa using
      (deriv_const_add_mul_add_sq_zero
        ((1 / (2 * mp.m)) * ‖z.2‖ ^ (2 : Nat) - gp.mu / ‖z.1‖)
        (z.2 1 / mp.m) (1 / (2 * mp.m)))
  · unfold partialP keplerHamiltonian energy
    change deriv
        (fun s : Real => (1 / (2 * mp.m)) * ‖z.2 + s • basisVec 2‖ ^ (2 : Nat) - gp.mu / ‖z.1‖)
        0 =
      z.2 2 / mp.m
    have hfun :
        (fun s : Real => (1 / (2 * mp.m)) * ‖z.2 + s • basisVec 2‖ ^ (2 : Nat) - gp.mu / ‖z.1‖) =
        fun s : Real =>
          ((1 / (2 * mp.m)) * ‖z.2‖ ^ (2 : Nat) - gp.mu / ‖z.1‖) +
            s * (z.2 2 / mp.m) + s ^ (2 : Nat) * (1 / (2 * mp.m)) := by
      funext s
      have hsq1 :
          ‖z.2 + s • basisVec 2‖ ^ (2 : Nat) =
            z.2 0 ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + (z.2 2 + s) ^ (2 : Nat) := by
        simpa [basisVec, Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) (z.2 + s • basisVec 2))
      have hsq2 :
          ‖z.2‖ ^ (2 : Nat) = z.2 0 ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
        simpa [Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.2)
      rw [hsq1, hsq2]
      ring
    rw [hfun]
    simpa using
      (deriv_const_add_mul_add_sq_zero
        ((1 / (2 * mp.m)) * ‖z.2‖ ^ (2 : Nat) - gp.mu / ‖z.1‖)
        (z.2 2 / mp.m) (1 / (2 * mp.m)))

lemma partialQ_keplerHamiltonian_of_radialDist_ne_zero
    (mp : MassParam) (gp : GravitationalParam) (i : Fin 3) (z : PhaseSpace)
    (h : radialDist z.1 ≠ 0) :
    partialQ (keplerHamiltonian mp gp) i z = gp.mu * z.1 i / (radialDist z.1) ^ (3 : Nat) := by
  let pos : Real -> Vec3 := fun s => z.1 + s • basisVec i
  have hpos :
      HasDerivAt pos (basisVec i) 0 := by
    simpa [pos, one_smul] using ((hasDerivAt_id (0 : Real)).smul_const (basisVec i)).const_add z.1
  have hnorm_sq :
      HasDerivAt (fun s : Real => radialDist (pos s) ^ (2 : Nat))
        (2 * inner ℝ (pos 0) (basisVec i)) 0 := by
    simpa [pos, radialDist] using hpos.norm_sq
  have hrad :
      HasDerivAt (fun s : Real => radialDist (pos s))
        (inner ℝ (pos 0) (basisVec i) / radialDist (pos 0)) 0 := by
    have hsqrt := hnorm_sq.sqrt (by simpa [pos] using pow_ne_zero 2 h)
    convert hsqrt using 1
    · funext s
      simp [pos, radialDist, pow_two]
    · field_simp [h]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (radialDist_nonneg (pos 0))]
  have hinv :
      HasDerivAt (fun s : Real => (radialDist (pos s))⁻¹)
        (-(inner ℝ (pos 0) (basisVec i) / radialDist (pos 0)) / radialDist (pos 0) ^ (2 : Nat)) 0 := by
    exact hrad.inv (by simpa [pos] using h)
  have hpot :
      HasDerivAt (fun s : Real => (-gp.mu) * (radialDist (pos s))⁻¹)
        ((-gp.mu) *
          (-(inner ℝ (pos 0) (basisVec i) / radialDist (pos 0)) / radialDist (pos 0) ^ (2 : Nat)))
        0 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hinv.const_mul (-gp.mu)
  have hconst :
      HasDerivAt (fun _ : Real => (1 / (2 * mp.m)) * radialDist z.2 ^ (2 : Nat)) 0 0 := by
    simpa using (hasDerivAt_const (0 : Real) ((1 / (2 * mp.m)) * radialDist z.2 ^ (2 : Nat)))
  have hsum := hconst.add hpot
  have hinner : inner ℝ z.1 (basisVec i) = z.1 i := by
    rw [inner_fin3]
    fin_cases i <;> simp [basisVec]
  have hvalue :
      (-gp.mu) *
          (-(inner ℝ (pos 0) (basisVec i) / radialDist (pos 0)) / radialDist (pos 0) ^ (2 : Nat)) =
        gp.mu * z.1 i / (radialDist z.1) ^ (3 : Nat) := by
    rw [show pos 0 = z.1 by simp [pos], hinner]
    simp
    field_simp [h]
  have hderiv :
      deriv
          (fun s : Real =>
            (1 / (2 * mp.m)) * radialDist z.2 ^ (2 : Nat) + (-gp.mu) * (radialDist (pos s))⁻¹)
          0 =
        (-gp.mu) *
          (-(inner ℝ (pos 0) (basisVec i) / radialDist (pos 0)) / radialDist (pos 0) ^ (2 : Nat)) := by
    convert hsum.deriv using 1
    ring
  calc
    partialQ (keplerHamiltonian mp gp) i z
        =
          deriv
            (fun s : Real =>
              (1 / (2 * mp.m)) * radialDist z.2 ^ (2 : Nat) + (-gp.mu) * (radialDist (pos s))⁻¹)
            0 := by
              simp [partialQ, keplerHamiltonian, energy, pos, div_eq_mul_inv, radialDist,
                sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
                mul_comm]
    _ = (-gp.mu) *
          (-(inner ℝ (pos 0) (basisVec i) / radialDist (pos 0)) / radialDist (pos 0) ^ (2 : Nat)) :=
      hderiv
    _ = gp.mu * z.1 i / (radialDist z.1) ^ (3 : Nat) := hvalue

theorem kepler_equations_poisson
    (mp : MassParam) (gp : GravitationalParam) (u : Vec3) (z : PhaseSpace)
    (hr : radialDist z.1 ≠ 0) :
    poissonBracket (X_u u) (keplerHamiltonian mp gp) z = (1 / mp.m) * P_u u z ∧
    poissonBracket (P_u u) (keplerHamiltonian mp gp) z =
      (-gp.mu / (radialDist z.1) ^ (3 : Nat)) * X_u u z := by
  have hp0 := partialP_keplerHamiltonian mp gp 0 z
  have hp1 := partialP_keplerHamiltonian mp gp 1 z
  have hp2 := partialP_keplerHamiltonian mp gp 2 z
  have hq0 := partialQ_keplerHamiltonian_of_radialDist_ne_zero mp gp 0 z hr
  have hq1 := partialQ_keplerHamiltonian_of_radialDist_ne_zero mp gp 1 z hr
  have hq2 := partialQ_keplerHamiltonian_of_radialDist_ne_zero mp gp 2 z hr
  constructor
  · unfold poissonBracket
    simp [partialQ_X_u, partialP_X_u, hp0, hp1, hp2, hq0, hq1, hq2, P_u]
    ring
  · unfold poissonBracket
    simp [partialQ_P_u, partialP_P_u, hp0, hp1, hp2, hq0, hq1, hq2, X_u]
    ring

theorem kepler_equations_poisson_vector
    (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace)
    (hr : radialDist z.1 ≠ 0) :
    (fun i : Fin 3 =>
      poissonBracket (fun z : PhaseSpace => z.1 i) (keplerHamiltonian mp gp) z) =
        (1 / mp.m) • z.2 ∧
    (fun i : Fin 3 =>
      poissonBracket (fun z : PhaseSpace => z.2 i) (keplerHamiltonian mp gp) z) =
        (-gp.mu / (radialDist z.1) ^ (3 : Nat)) • z.1 := by
  constructor
  · ext i
    have hi := (kepler_equations_poisson mp gp (basisVec i) z hr).1
    have hXi : X_u (basisVec i) = fun z : PhaseSpace => z.1 i := by
      funext z
      fin_cases i <;> simp [X_u, basisVec]
    have hPi : P_u (basisVec i) = fun z : PhaseSpace => z.2 i := by
      funext z
      fin_cases i <;> simp [P_u, basisVec]
    rw [← hXi]
    simpa [hPi] using hi
  · ext i
    have hi := (kepler_equations_poisson mp gp (basisVec i) z hr).2
    have hPi : P_u (basisVec i) = fun z : PhaseSpace => z.2 i := by
      funext z
      fin_cases i <;> simp [P_u, basisVec]
    have hXi : X_u (basisVec i) = fun z : PhaseSpace => z.1 i := by
      funext z
      fin_cases i <;> simp [X_u, basisVec]
    rw [← hPi]
    simpa [hXi] using hi

lemma poisson_L_u_H (mp : MassParam) (gp : GravitationalParam) (u : Vec3) (z : PhaseSpace) :
    poissonBracket (L_u u) (keplerHamiltonian mp gp) z = 0 := by
  have hp0 := partialP_keplerHamiltonian mp gp 0 z
  have hp1 := partialP_keplerHamiltonian mp gp 1 z
  have hp2 := partialP_keplerHamiltonian mp gp 2 z
  by_cases hq : radialDist z.1 = 0
  · have hz0 : z.1 = 0 := (radialDist_eq_zero_iff _).mp hq
    simp [poissonBracket, partialQ_L_u_0, partialQ_L_u_1, partialQ_L_u_2,
      partialP_L_u_0, partialP_L_u_1, partialP_L_u_2, hp0, hp1, hp2, hz0]
    ring_nf
  · have hq0 := partialQ_keplerHamiltonian_of_radialDist_ne_zero mp gp 0 z hq
    have hq1 := partialQ_keplerHamiltonian_of_radialDist_ne_zero mp gp 1 z hq
    have hq2 := partialQ_keplerHamiltonian_of_radialDist_ne_zero mp gp 2 z hq
    simp [poissonBracket, partialQ_L_u_0, partialQ_L_u_1, partialQ_L_u_2,
      partialP_L_u_0, partialP_L_u_1, partialP_L_u_2, hp0, hp1, hp2, hq0, hq1, hq2]
    ring_nf

lemma poisson_L_u_L_v (u v : Vec3) (z : PhaseSpace) :
    poissonBracket (L_u u) (L_u v) z = L_u (cross u v) z := by
  simp [poissonBracket, L_u, L0, L1, L2, cross, cross_apply,
    partialQ_L_u_0, partialQ_L_u_1, partialQ_L_u_2,
    partialP_L_u_0, partialP_L_u_1, partialP_L_u_2]
  ring_nf

lemma partialQ_F_u (u : Vec3) (i : Fin 3) (z : PhaseSpace) :
    partialQ
        (fun z : PhaseSpace => radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
        i z =
      radialDist z.2 ^ (2 : Nat) * u i - z.2 i * P_u u z := by
  fin_cases i
  · unfold partialQ
    change deriv
        (fun s : Real =>
          radialDist z.2 ^ (2 : Nat) * X_u u (z.1 + s • basisVec 0, z.2) -
            inner ℝ (z.1 + s • basisVec 0) z.2 * P_u u (z.1 + s • basisVec 0, z.2))
        0 =
      radialDist z.2 ^ (2 : Nat) * u 0 - z.2 0 * P_u u z
    have hfun :
        (fun s : Real =>
          radialDist z.2 ^ (2 : Nat) * X_u u (z.1 + s • basisVec 0, z.2) -
            inner ℝ (z.1 + s • basisVec 0) z.2 * P_u u (z.1 + s • basisVec 0, z.2))
          =
        fun s : Real =>
          (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z) +
            s * (radialDist z.2 ^ (2 : Nat) * u 0 - z.2 0 * P_u u z) := by
      funext s
      repeat rw [inner_fin3]
      simp [X_u, P_u, basisVec]
      ring_nf
    rw [hfun]
    simpa using
      (deriv_const_add_mul_zero
        (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
        (radialDist z.2 ^ (2 : Nat) * u 0 - z.2 0 * P_u u z))
  · unfold partialQ
    change deriv
        (fun s : Real =>
          radialDist z.2 ^ (2 : Nat) * X_u u (z.1 + s • basisVec 1, z.2) -
            inner ℝ (z.1 + s • basisVec 1) z.2 * P_u u (z.1 + s • basisVec 1, z.2))
        0 =
      radialDist z.2 ^ (2 : Nat) * u 1 - z.2 1 * P_u u z
    have hfun :
        (fun s : Real =>
          radialDist z.2 ^ (2 : Nat) * X_u u (z.1 + s • basisVec 1, z.2) -
            inner ℝ (z.1 + s • basisVec 1) z.2 * P_u u (z.1 + s • basisVec 1, z.2))
          =
        fun s : Real =>
          (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z) +
            s * (radialDist z.2 ^ (2 : Nat) * u 1 - z.2 1 * P_u u z) := by
      funext s
      repeat rw [inner_fin3]
      simp [X_u, P_u, basisVec]
      ring_nf
    rw [hfun]
    simpa using
      (deriv_const_add_mul_zero
        (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
        (radialDist z.2 ^ (2 : Nat) * u 1 - z.2 1 * P_u u z))
  · unfold partialQ
    change deriv
        (fun s : Real =>
          radialDist z.2 ^ (2 : Nat) * X_u u (z.1 + s • basisVec 2, z.2) -
            inner ℝ (z.1 + s • basisVec 2) z.2 * P_u u (z.1 + s • basisVec 2, z.2))
        0 =
      radialDist z.2 ^ (2 : Nat) * u 2 - z.2 2 * P_u u z
    have hfun :
        (fun s : Real =>
          radialDist z.2 ^ (2 : Nat) * X_u u (z.1 + s • basisVec 2, z.2) -
            inner ℝ (z.1 + s • basisVec 2) z.2 * P_u u (z.1 + s • basisVec 2, z.2))
          =
        fun s : Real =>
          (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z) +
            s * (radialDist z.2 ^ (2 : Nat) * u 2 - z.2 2 * P_u u z) := by
      funext s
      repeat rw [inner_fin3]
      simp [X_u, P_u, basisVec]
      ring_nf
    rw [hfun]
    simpa using
      (deriv_const_add_mul_zero
        (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
        (radialDist z.2 ^ (2 : Nat) * u 2 - z.2 2 * P_u u z))

lemma partialP_F_u (u : Vec3) (i : Fin 3) (z : PhaseSpace) :
    partialP
        (fun z : PhaseSpace => radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
        i z =
      2 * z.2 i * X_u u z - z.1 i * P_u u z - inner ℝ z.1 z.2 * u i := by
  fin_cases i
  · unfold partialP
    change deriv
        (fun s : Real =>
          radialDist (z.2 + s • basisVec 0) ^ (2 : Nat) * X_u u (z.1, z.2 + s • basisVec 0) -
            inner ℝ z.1 (z.2 + s • basisVec 0) * P_u u (z.1, z.2 + s • basisVec 0))
        0 =
      2 * z.2 0 * X_u u z - z.1 0 * P_u u z - inner ℝ z.1 z.2 * u 0
    have hfun :
        (fun s : Real =>
          radialDist (z.2 + s • basisVec 0) ^ (2 : Nat) * X_u u (z.1, z.2 + s • basisVec 0) -
            inner ℝ z.1 (z.2 + s • basisVec 0) * P_u u (z.1, z.2 + s • basisVec 0))
          =
        fun s : Real =>
          (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z) +
            s * (2 * z.2 0 * X_u u z - z.1 0 * P_u u z - inner ℝ z.1 z.2 * u 0) +
            s ^ (2 : Nat) * (X_u u z - z.1 0 * u 0) := by
      funext s
      have hsq1 :
          radialDist (z.2 + s • basisVec 0) ^ (2 : Nat) =
            (z.2 0 + s) ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
        simpa [radialDist, basisVec, Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) (z.2 + s • basisVec 0))
      have hsq2 :
          radialDist z.2 ^ (2 : Nat) = z.2 0 ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
        simpa [radialDist, Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.2)
      repeat rw [inner_fin3]
      rw [hsq1, hsq2]
      simp [X_u, P_u, basisVec]
      ring_nf
    rw [hfun]
    simpa using
      (deriv_const_add_mul_add_sq_zero
        (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
        (2 * z.2 0 * X_u u z - z.1 0 * P_u u z - inner ℝ z.1 z.2 * u 0)
        (X_u u z - z.1 0 * u 0))
  · unfold partialP
    change deriv
        (fun s : Real =>
          radialDist (z.2 + s • basisVec 1) ^ (2 : Nat) * X_u u (z.1, z.2 + s • basisVec 1) -
            inner ℝ z.1 (z.2 + s • basisVec 1) * P_u u (z.1, z.2 + s • basisVec 1))
        0 =
      2 * z.2 1 * X_u u z - z.1 1 * P_u u z - inner ℝ z.1 z.2 * u 1
    have hfun :
        (fun s : Real =>
          radialDist (z.2 + s • basisVec 1) ^ (2 : Nat) * X_u u (z.1, z.2 + s • basisVec 1) -
            inner ℝ z.1 (z.2 + s • basisVec 1) * P_u u (z.1, z.2 + s • basisVec 1))
          =
        fun s : Real =>
          (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z) +
            s * (2 * z.2 1 * X_u u z - z.1 1 * P_u u z - inner ℝ z.1 z.2 * u 1) +
            s ^ (2 : Nat) * (X_u u z - z.1 1 * u 1) := by
      funext s
      have hsq1 :
          radialDist (z.2 + s • basisVec 1) ^ (2 : Nat) =
            z.2 0 ^ (2 : Nat) + (z.2 1 + s) ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
        simpa [radialDist, basisVec, Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) (z.2 + s • basisVec 1))
      have hsq2 :
          radialDist z.2 ^ (2 : Nat) = z.2 0 ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
        simpa [radialDist, Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.2)
      repeat rw [inner_fin3]
      rw [hsq1, hsq2]
      simp [X_u, P_u, basisVec]
      ring_nf
    rw [hfun]
    simpa using
      (deriv_const_add_mul_add_sq_zero
        (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
        (2 * z.2 1 * X_u u z - z.1 1 * P_u u z - inner ℝ z.1 z.2 * u 1)
        (X_u u z - z.1 1 * u 1))
  · unfold partialP
    change deriv
        (fun s : Real =>
          radialDist (z.2 + s • basisVec 2) ^ (2 : Nat) * X_u u (z.1, z.2 + s • basisVec 2) -
            inner ℝ z.1 (z.2 + s • basisVec 2) * P_u u (z.1, z.2 + s • basisVec 2))
        0 =
      2 * z.2 2 * X_u u z - z.1 2 * P_u u z - inner ℝ z.1 z.2 * u 2
    have hfun :
        (fun s : Real =>
          radialDist (z.2 + s • basisVec 2) ^ (2 : Nat) * X_u u (z.1, z.2 + s • basisVec 2) -
            inner ℝ z.1 (z.2 + s • basisVec 2) * P_u u (z.1, z.2 + s • basisVec 2))
          =
        fun s : Real =>
          (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z) +
            s * (2 * z.2 2 * X_u u z - z.1 2 * P_u u z - inner ℝ z.1 z.2 * u 2) +
            s ^ (2 : Nat) * (X_u u z - z.1 2 * u 2) := by
      funext s
      have hsq1 :
          radialDist (z.2 + s • basisVec 2) ^ (2 : Nat) =
            z.2 0 ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + (z.2 2 + s) ^ (2 : Nat) := by
        simpa [radialDist, basisVec, Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) (z.2 + s • basisVec 2))
      have hsq2 :
          radialDist z.2 ^ (2 : Nat) = z.2 0 ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
        simpa [radialDist, Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.2)
      repeat rw [inner_fin3]
      rw [hsq1, hsq2]
      simp [X_u, P_u, basisVec]
      ring_nf
    rw [hfun]
    simpa using
      (deriv_const_add_mul_add_sq_zero
        (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
        (2 * z.2 2 * X_u u z - z.1 2 * P_u u z - inner ℝ z.1 z.2 * u 2)
        (X_u u z - z.1 2 * u 2))

lemma partialQ_U_scalar_of_radialDist_ne_zero (u : Vec3) (i : Fin 3) (z : PhaseSpace)
    (h : radialDist z.1 ≠ 0) :
    partialQ (fun z : PhaseSpace => X_u u z / radialDist z.1) i z =
      u i / radialDist z.1 - X_u u z * z.1 i / (radialDist z.1) ^ (3 : Nat) := by
  let xpos : Real -> Real := fun s => X_u u (z.1 + s • basisVec i, z.2)
  have hX : HasDerivAt xpos (u i) 0 := by
    fin_cases i
    · change HasDerivAt xpos (u 0) 0
      have hfun :
          xpos = fun s : Real => X_u u z + s * u 0 := by
        funext s
        simp [xpos, X_u, basisVec]
        ring_nf
      rw [hfun]
      simpa using ((hasDerivAt_id (0 : Real)).mul_const (u 0)).const_add (X_u u z)
    · change HasDerivAt xpos (u 1) 0
      have hfun :
          xpos = fun s : Real => X_u u z + s * u 1 := by
        funext s
        simp [xpos, X_u, basisVec]
        ring_nf
      rw [hfun]
      simpa using ((hasDerivAt_id (0 : Real)).mul_const (u 1)).const_add (X_u u z)
    · change HasDerivAt xpos (u 2) 0
      have hfun :
          xpos = fun s : Real => X_u u z + s * u 2 := by
        funext s
        simp [xpos, X_u, basisVec]
        ring_nf
      rw [hfun]
      simpa using ((hasDerivAt_id (0 : Real)).mul_const (u 2)).const_add (X_u u z)
  let pos : Real -> Vec3 := fun s => z.1 + s • basisVec i
  have hpos :
      HasDerivAt pos (basisVec i) 0 := by
    simpa [pos, one_smul] using ((hasDerivAt_id (0 : Real)).smul_const (basisVec i)).const_add z.1
  have hnorm_sq :
      HasDerivAt (fun s : Real => radialDist (pos s) ^ (2 : Nat))
        (2 * inner ℝ (pos 0) (basisVec i)) 0 := by
    simpa [pos, radialDist] using hpos.norm_sq
  have hrad :
      HasDerivAt (fun s : Real => radialDist (pos s))
        (inner ℝ (pos 0) (basisVec i) / radialDist (pos 0)) 0 := by
    have hsqrt := hnorm_sq.sqrt (by simpa [pos] using pow_ne_zero 2 h)
    convert hsqrt using 1
    · funext s
      simp [pos, radialDist, pow_two]
    · field_simp [h]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (radialDist_nonneg (pos 0))]
  have hInv :
      HasDerivAt (fun s : Real => (radialDist (pos s))⁻¹)
        (-(z.1 i) / (radialDist z.1) ^ (3 : Nat)) 0 := by
    have hinv :
        HasDerivAt (fun s : Real => (radialDist (pos s))⁻¹)
          (-(inner ℝ (pos 0) (basisVec i) / radialDist (pos 0)) / radialDist (pos 0) ^ (2 : Nat))
          0 := by
      exact hrad.inv (by simpa [pos] using h)
    have hinner : inner ℝ z.1 (basisVec i) = z.1 i := by
      rw [inner_fin3]
      fin_cases i <;> simp [basisVec]
    have hvalue :
        (-(inner ℝ (pos 0) (basisVec i) / radialDist (pos 0)) / radialDist (pos 0) ^ (2 : Nat)) =
          -(z.1 i) / (radialDist z.1) ^ (3 : Nat) := by
      rw [show pos 0 = z.1 by simp [pos], hinner]
      field_simp [h]
    exact hvalue.symm ▸ hinv
  have hprod :
      HasDerivAt (fun s : Real => xpos s * (radialDist (pos s))⁻¹)
        (u i * (radialDist z.1)⁻¹ + xpos 0 * (-(z.1 i) / (radialDist z.1) ^ (3 : Nat))) 0 := by
    simpa [pos] using hX.mul hInv
  have hvalue :
      u i * (radialDist z.1)⁻¹ + xpos 0 * (-(z.1 i) / (radialDist z.1) ^ (3 : Nat)) =
        u i / radialDist z.1 - X_u u z * z.1 i / (radialDist z.1) ^ (3 : Nat) := by
    simp [xpos, div_eq_mul_inv, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
  exact hvalue.symm ▸ (by
    simpa [partialQ, xpos, pos, div_eq_mul_inv] using hprod.deriv)

lemma partialP_U_scalar (u : Vec3) (i : Fin 3) (z : PhaseSpace) :
    partialP (fun z : PhaseSpace => X_u u z / radialDist z.1) i z = 0 := by
  unfold partialP
  simp [X_u, div_eq_mul_inv]

lemma hasDerivAt_qPath_F_u (u : Vec3) (i : Fin 3) (z : PhaseSpace) :
    HasDerivAt
      (fun s : Real =>
        (fun z : PhaseSpace => radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
          (z.1 + s • basisVec i, z.2))
      (radialDist z.2 ^ (2 : Nat) * u i - z.2 i * P_u u z) 0 := by
  fin_cases i
  · have hfun :
        (fun s : Real =>
          radialDist z.2 ^ (2 : Nat) * X_u u (z.1 + s • basisVec 0, z.2) -
            inner ℝ (z.1 + s • basisVec 0) z.2 * P_u u (z.1 + s • basisVec 0, z.2))
          =
        fun s : Real =>
          (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z) +
            s * (radialDist z.2 ^ (2 : Nat) * u 0 - z.2 0 * P_u u z) := by
      funext s
      repeat rw [inner_fin3]
      simp [X_u, P_u, basisVec]
      ring_nf
    change HasDerivAt
      (fun s : Real =>
        radialDist z.2 ^ (2 : Nat) * X_u u (z.1 + s • basisVec 0, z.2) -
          inner ℝ (z.1 + s • basisVec 0) z.2 * P_u u (z.1 + s • basisVec 0, z.2))
      (radialDist z.2 ^ (2 : Nat) * u 0 - z.2 0 * P_u u z) 0
    rw [hfun]
    exact
      hasDerivAt_const_add_mul_zero
        (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
        (radialDist z.2 ^ (2 : Nat) * u 0 - z.2 0 * P_u u z)
  · have hfun :
        (fun s : Real =>
          radialDist z.2 ^ (2 : Nat) * X_u u (z.1 + s • basisVec 1, z.2) -
            inner ℝ (z.1 + s • basisVec 1) z.2 * P_u u (z.1 + s • basisVec 1, z.2))
          =
        fun s : Real =>
          (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z) +
            s * (radialDist z.2 ^ (2 : Nat) * u 1 - z.2 1 * P_u u z) := by
      funext s
      repeat rw [inner_fin3]
      simp [X_u, P_u, basisVec]
      ring_nf
    change HasDerivAt
      (fun s : Real =>
        radialDist z.2 ^ (2 : Nat) * X_u u (z.1 + s • basisVec 1, z.2) -
          inner ℝ (z.1 + s • basisVec 1) z.2 * P_u u (z.1 + s • basisVec 1, z.2))
      (radialDist z.2 ^ (2 : Nat) * u 1 - z.2 1 * P_u u z) 0
    rw [hfun]
    exact
      hasDerivAt_const_add_mul_zero
        (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
        (radialDist z.2 ^ (2 : Nat) * u 1 - z.2 1 * P_u u z)
  · have hfun :
        (fun s : Real =>
          radialDist z.2 ^ (2 : Nat) * X_u u (z.1 + s • basisVec 2, z.2) -
            inner ℝ (z.1 + s • basisVec 2) z.2 * P_u u (z.1 + s • basisVec 2, z.2))
          =
        fun s : Real =>
          (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z) +
            s * (radialDist z.2 ^ (2 : Nat) * u 2 - z.2 2 * P_u u z) := by
      funext s
      repeat rw [inner_fin3]
      simp [X_u, P_u, basisVec]
      ring_nf
    change HasDerivAt
      (fun s : Real =>
        radialDist z.2 ^ (2 : Nat) * X_u u (z.1 + s • basisVec 2, z.2) -
          inner ℝ (z.1 + s • basisVec 2) z.2 * P_u u (z.1 + s • basisVec 2, z.2))
      (radialDist z.2 ^ (2 : Nat) * u 2 - z.2 2 * P_u u z) 0
    rw [hfun]
    exact
      hasDerivAt_const_add_mul_zero
        (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
        (radialDist z.2 ^ (2 : Nat) * u 2 - z.2 2 * P_u u z)

lemma hasDerivAt_pPath_F_u (u : Vec3) (i : Fin 3) (z : PhaseSpace) :
    HasDerivAt
      (fun s : Real =>
        (fun z : PhaseSpace => radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
          (z.1, z.2 + s • basisVec i))
      (2 * z.2 i * X_u u z - z.1 i * P_u u z - inner ℝ z.1 z.2 * u i) 0 := by
  fin_cases i
  · have hfun :
        (fun s : Real =>
          radialDist (z.2 + s • basisVec 0) ^ (2 : Nat) * X_u u (z.1, z.2 + s • basisVec 0) -
            inner ℝ z.1 (z.2 + s • basisVec 0) * P_u u (z.1, z.2 + s • basisVec 0))
          =
        fun s : Real =>
          (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z) +
            s * (2 * z.2 0 * X_u u z - z.1 0 * P_u u z - inner ℝ z.1 z.2 * u 0) +
            s ^ (2 : Nat) * (X_u u z - z.1 0 * u 0) := by
      funext s
      have hsq1 :
          radialDist (z.2 + s • basisVec 0) ^ (2 : Nat) =
            (z.2 0 + s) ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
        simpa [radialDist, basisVec, Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) (z.2 + s • basisVec 0))
      have hsq2 :
          radialDist z.2 ^ (2 : Nat) = z.2 0 ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
        simpa [radialDist, Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.2)
      repeat rw [inner_fin3]
      rw [hsq1, hsq2]
      simp [X_u, P_u, basisVec]
      ring_nf
    change HasDerivAt
      (fun s : Real =>
        radialDist (z.2 + s • basisVec 0) ^ (2 : Nat) * X_u u (z.1, z.2 + s • basisVec 0) -
          inner ℝ z.1 (z.2 + s • basisVec 0) * P_u u (z.1, z.2 + s • basisVec 0))
      (2 * z.2 0 * X_u u z - z.1 0 * P_u u z - inner ℝ z.1 z.2 * u 0) 0
    rw [hfun]
    exact
      hasDerivAt_const_add_mul_add_sq_zero
        (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
        (2 * z.2 0 * X_u u z - z.1 0 * P_u u z - inner ℝ z.1 z.2 * u 0)
        (X_u u z - z.1 0 * u 0)
  · have hfun :
        (fun s : Real =>
          radialDist (z.2 + s • basisVec 1) ^ (2 : Nat) * X_u u (z.1, z.2 + s • basisVec 1) -
            inner ℝ z.1 (z.2 + s • basisVec 1) * P_u u (z.1, z.2 + s • basisVec 1))
          =
        fun s : Real =>
          (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z) +
            s * (2 * z.2 1 * X_u u z - z.1 1 * P_u u z - inner ℝ z.1 z.2 * u 1) +
            s ^ (2 : Nat) * (X_u u z - z.1 1 * u 1) := by
      funext s
      have hsq1 :
          radialDist (z.2 + s • basisVec 1) ^ (2 : Nat) =
            z.2 0 ^ (2 : Nat) + (z.2 1 + s) ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
        simpa [radialDist, basisVec, Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) (z.2 + s • basisVec 1))
      have hsq2 :
          radialDist z.2 ^ (2 : Nat) = z.2 0 ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
        simpa [radialDist, Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.2)
      repeat rw [inner_fin3]
      rw [hsq1, hsq2]
      simp [X_u, P_u, basisVec]
      ring_nf
    change HasDerivAt
      (fun s : Real =>
        radialDist (z.2 + s • basisVec 1) ^ (2 : Nat) * X_u u (z.1, z.2 + s • basisVec 1) -
          inner ℝ z.1 (z.2 + s • basisVec 1) * P_u u (z.1, z.2 + s • basisVec 1))
      (2 * z.2 1 * X_u u z - z.1 1 * P_u u z - inner ℝ z.1 z.2 * u 1) 0
    rw [hfun]
    exact
      hasDerivAt_const_add_mul_add_sq_zero
        (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
        (2 * z.2 1 * X_u u z - z.1 1 * P_u u z - inner ℝ z.1 z.2 * u 1)
        (X_u u z - z.1 1 * u 1)
  · have hfun :
        (fun s : Real =>
          radialDist (z.2 + s • basisVec 2) ^ (2 : Nat) * X_u u (z.1, z.2 + s • basisVec 2) -
            inner ℝ z.1 (z.2 + s • basisVec 2) * P_u u (z.1, z.2 + s • basisVec 2))
          =
        fun s : Real =>
          (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z) +
            s * (2 * z.2 2 * X_u u z - z.1 2 * P_u u z - inner ℝ z.1 z.2 * u 2) +
            s ^ (2 : Nat) * (X_u u z - z.1 2 * u 2) := by
      funext s
      have hsq1 :
          radialDist (z.2 + s • basisVec 2) ^ (2 : Nat) =
            z.2 0 ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + (z.2 2 + s) ^ (2 : Nat) := by
        simpa [radialDist, basisVec, Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) (z.2 + s • basisVec 2))
      have hsq2 :
          radialDist z.2 ^ (2 : Nat) = z.2 0 ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
        simpa [radialDist, Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.2)
      repeat rw [inner_fin3]
      rw [hsq1, hsq2]
      simp [X_u, P_u, basisVec]
      ring_nf
    change HasDerivAt
      (fun s : Real =>
        radialDist (z.2 + s • basisVec 2) ^ (2 : Nat) * X_u u (z.1, z.2 + s • basisVec 2) -
          inner ℝ z.1 (z.2 + s • basisVec 2) * P_u u (z.1, z.2 + s • basisVec 2))
      (2 * z.2 2 * X_u u z - z.1 2 * P_u u z - inner ℝ z.1 z.2 * u 2) 0
    rw [hfun]
    exact
      hasDerivAt_const_add_mul_add_sq_zero
        (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
        (2 * z.2 2 * X_u u z - z.1 2 * P_u u z - inner ℝ z.1 z.2 * u 2)
        (X_u u z - z.1 2 * u 2)

lemma hasDerivAt_qPath_U_scalar_of_radialDist_ne_zero (u : Vec3) (i : Fin 3) (z : PhaseSpace)
    (h : radialDist z.1 ≠ 0) :
    HasDerivAt
      (fun s : Real =>
        (fun z : PhaseSpace => X_u u z / radialDist z.1) (z.1 + s • basisVec i, z.2))
      (u i / radialDist z.1 - X_u u z * z.1 i / (radialDist z.1) ^ (3 : Nat)) 0 := by
  let xpos : Real -> Real := fun s => X_u u (z.1 + s • basisVec i, z.2)
  have hX : HasDerivAt xpos (u i) 0 := by
    fin_cases i
    · change HasDerivAt xpos (u 0) 0
      have hfun : xpos = fun s : Real => X_u u z + s * u 0 := by
        funext s
        simp [xpos, X_u, basisVec]
        ring_nf
      rw [hfun]
      exact hasDerivAt_const_add_mul_zero (X_u u z) (u 0)
    · change HasDerivAt xpos (u 1) 0
      have hfun : xpos = fun s : Real => X_u u z + s * u 1 := by
        funext s
        simp [xpos, X_u, basisVec]
        ring_nf
      rw [hfun]
      exact hasDerivAt_const_add_mul_zero (X_u u z) (u 1)
    · change HasDerivAt xpos (u 2) 0
      have hfun : xpos = fun s : Real => X_u u z + s * u 2 := by
        funext s
        simp [xpos, X_u, basisVec]
        ring_nf
      rw [hfun]
      exact hasDerivAt_const_add_mul_zero (X_u u z) (u 2)
  let pos : Real -> Vec3 := fun s => z.1 + s • basisVec i
  have hpos :
      HasDerivAt pos (basisVec i) 0 := by
    simpa [pos, one_smul] using ((hasDerivAt_id (0 : Real)).smul_const (basisVec i)).const_add z.1
  have hnorm_sq :
      HasDerivAt (fun s : Real => radialDist (pos s) ^ (2 : Nat))
        (2 * inner ℝ (pos 0) (basisVec i)) 0 := by
    simpa [pos, radialDist] using hpos.norm_sq
  have hrad :
      HasDerivAt (fun s : Real => radialDist (pos s))
        (inner ℝ (pos 0) (basisVec i) / radialDist (pos 0)) 0 := by
    have hsqrt := hnorm_sq.sqrt (by simpa [pos] using pow_ne_zero 2 h)
    convert hsqrt using 1
    · funext s
      simp [pos, radialDist, pow_two]
    · field_simp [h]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (radialDist_nonneg (pos 0))]
  have hInv :
      HasDerivAt (fun s : Real => (radialDist (pos s))⁻¹)
        (-(z.1 i) / (radialDist z.1) ^ (3 : Nat)) 0 := by
    have hinv :
        HasDerivAt (fun s : Real => (radialDist (pos s))⁻¹)
          (-(inner ℝ (pos 0) (basisVec i) / radialDist (pos 0)) / radialDist (pos 0) ^ (2 : Nat))
          0 := by
      exact hrad.inv (by simpa [pos] using h)
    have hinner : inner ℝ z.1 (basisVec i) = z.1 i := by
      rw [inner_fin3]
      fin_cases i <;> simp [basisVec]
    have hvalue :
        (-(inner ℝ (pos 0) (basisVec i) / radialDist (pos 0)) / radialDist (pos 0) ^ (2 : Nat)) =
          -(z.1 i) / (radialDist z.1) ^ (3 : Nat) := by
      rw [show pos 0 = z.1 by simp [pos], hinner]
      field_simp [h]
    exact hvalue.symm ▸ hinv
  have hprod :
      HasDerivAt (fun s : Real => xpos s * (radialDist (pos s))⁻¹)
        (u i * (radialDist z.1)⁻¹ + xpos 0 * (-(z.1 i) / (radialDist z.1) ^ (3 : Nat))) 0 := by
    simpa [pos] using hX.mul hInv
  have hvalue :
      u i * (radialDist z.1)⁻¹ + xpos 0 * (-(z.1 i) / (radialDist z.1) ^ (3 : Nat)) =
        u i / radialDist z.1 - X_u u z * z.1 i / (radialDist z.1) ^ (3 : Nat) := by
    simp [xpos, div_eq_mul_inv, sub_eq_add_neg, mul_left_comm, mul_comm]
  exact hvalue.symm ▸ (by
    simpa [xpos, pos, div_eq_mul_inv] using hprod)

lemma hasDerivAt_pPath_U_scalar (u : Vec3) (i : Fin 3) (z : PhaseSpace) :
    HasDerivAt
      (fun s : Real =>
        (fun z : PhaseSpace => X_u u z / radialDist z.1) (z.1, z.2 + s • basisVec i))
      0 0 := by
  simpa [X_u, div_eq_mul_inv] using
    (hasDerivAt_const (0 : Real) ((fun z : PhaseSpace => X_u u z / radialDist z.1) z))

lemma A_u_eq_observables (mp : MassParam) (gp : GravitationalParam) (u : Vec3) :
    A_u mp gp u =
      fun z : PhaseSpace =>
        (radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z) -
          (mp.m * gp.mu) * (X_u u z / radialDist z.1) := by
  funext w
  have hp2 :
      radialDist w.2 ^ (2 : Nat) = w.2 0 ^ (2 : Nat) + w.2 1 ^ (2 : Nat) + w.2 2 ^ (2 : Nat) := by
    simpa [radialDist, Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq (n := Fin 3) w.2)
  simp [A_u, A0, A1, A2, F0, F1, F2, U0, U1, U2, X_u, P_u, L0, L1, L2, inner_fin3, hp2,
    div_eq_mul_inv]
  ring_nf

lemma partialQ_A_u_of_radialDist_ne_zero
    (mp : MassParam) (gp : GravitationalParam) (u : Vec3) (i : Fin 3) (z : PhaseSpace)
    (h : radialDist z.1 ≠ 0) :
    partialQ (A_u mp gp u) i z =
      (radialDist z.2 ^ (2 : Nat) * u i - z.2 i * P_u u z) -
        (mp.m * gp.mu) * (u i / radialDist z.1 - X_u u z * z.1 i / (radialDist z.1) ^ (3 : Nat)) := by
  rw [A_u_eq_observables]
  have hf : HasDerivAt
      (fun s : Real =>
        radialDist z.2 ^ (2 : Nat) * X_u u (z.1 + s • basisVec i, z.2) -
          inner ℝ (z.1 + s • basisVec i) z.2 * P_u u (z.1 + s • basisVec i, z.2))
      (radialDist z.2 ^ (2 : Nat) * u i - z.2 i * P_u u z) 0 := by
    simpa using hasDerivAt_qPath_F_u u i z
  have hg : HasDerivAt
      (fun s : Real => X_u u (z.1 + s • basisVec i, z.2) / radialDist (z.1 + s • basisVec i))
      (u i / radialDist z.1 - X_u u z * z.1 i / (radialDist z.1) ^ (3 : Nat)) 0 := by
    simpa using hasDerivAt_qPath_U_scalar_of_radialDist_ne_zero u i z h
  simpa [partialQ, div_eq_mul_inv] using (hf.sub (hg.const_mul (mp.m * gp.mu))).deriv

lemma partialQ_A_u_of_radialDist_ne_zero_div
    (mp : MassParam) (gp : GravitationalParam) (u : Vec3) (i : Fin 3) (z : PhaseSpace)
    (h : radialDist z.1 ≠ 0) :
    partialQ (A_u mp gp u) i z =
      (radialDist z.2 ^ (2 : Nat) * u i - z.2 i * P_u u z) -
        (mp.m * gp.mu) *
          ((u i * radialDist z.1 ^ (2 : Nat) - X_u u z * z.1 i) / (radialDist z.1) ^ (3 : Nat)) := by
  rw [partialQ_A_u_of_radialDist_ne_zero mp gp u i z h]
  have hz : radialDist z.1 ≠ 0 := h
  congr 1
  field_simp [hz]

lemma partialP_A_u
    (mp : MassParam) (gp : GravitationalParam) (u : Vec3) (i : Fin 3) (z : PhaseSpace) :
    partialP (A_u mp gp u) i z =
      2 * z.2 i * X_u u z - z.1 i * P_u u z - inner ℝ z.1 z.2 * u i := by
  rw [A_u_eq_observables]
  have hf : HasDerivAt
      (fun s : Real =>
        radialDist (z.2 + s • basisVec i) ^ (2 : Nat) * X_u u (z.1, z.2 + s • basisVec i) -
          inner ℝ z.1 (z.2 + s • basisVec i) * P_u u (z.1, z.2 + s • basisVec i))
      (2 * z.2 i * X_u u z - z.1 i * P_u u z - inner ℝ z.1 z.2 * u i) 0 := by
    simpa using hasDerivAt_pPath_F_u u i z
  have hg : HasDerivAt
      (fun s : Real => X_u u (z.1, z.2 + s • basisVec i) / radialDist z.1)
      0 0 := by
    simpa using hasDerivAt_pPath_U_scalar u i z
  simpa [partialP, div_eq_mul_inv] using (hf.sub (hg.const_mul (mp.m * gp.mu))).deriv

lemma poisson_A_u_H (mp : MassParam) (gp : GravitationalParam) (u : Vec3) (z : PhaseSpace)
    (h : radialDist z.1 ≠ 0) :
    poissonBracket (A_u mp gp u) (keplerHamiltonian mp gp) z = 0 := by
  let Fobs : PhaseSpace -> Real :=
    fun z => radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z
  let Uobs : PhaseSpace -> Real :=
    fun z => X_u u z / radialDist z.1
  have hA :
      A_u mp gp u = fun z : PhaseSpace => Fobs z - (mp.m * gp.mu) * Uobs z := by
    funext w
    have hF :
        (u 0) * F0 w + (u 1) * F1 w + (u 2) * F2 w = Fobs w := by
      have hsq :
          radialDist w.2 ^ (2 : Nat) = w.2 0 ^ (2 : Nat) + w.2 1 ^ (2 : Nat) + w.2 2 ^ (2 : Nat) := by
        simpa [radialDist, Fin.sum_univ_three] using
          (EuclideanSpace.real_norm_sq_eq (n := Fin 3) w.2)
      simp [Fobs, hsq, X_u, P_u, F0, F1, F2, L0, L1, L2, inner_fin3]
      ring_nf
    have hU :
        (u 0) * U0 mp gp w + (u 1) * U1 mp gp w + (u 2) * U2 mp gp w =
          (mp.m * gp.mu) * Uobs w := by
      simp [Uobs, U0, U1, U2, X_u, div_eq_mul_inv]
      ring_nf
    calc
      A_u mp gp u w
          = ((u 0) * F0 w + (u 1) * F1 w + (u 2) * F2 w) -
              ((u 0) * U0 mp gp w + (u 1) * U1 mp gp w + (u 2) * U2 mp gp w) := by
                simp [A_u, A0, A1, A2]
                ring
      _ = Fobs w - (mp.m * gp.mu) * Uobs w := by
            rw [hF, hU]
  have hAq :
      ∀ i : Fin 3,
        partialQ (A_u mp gp u) i z =
          (radialDist z.2 ^ (2 : Nat) * u i - z.2 i * P_u u z) -
            (mp.m * gp.mu) * (u i / radialDist z.1 - X_u u z * z.1 i / (radialDist z.1) ^ (3 : Nat)) := by
    intro i
    rw [hA]
    have hf : HasDerivAt
        (fun s : Real => Fobs (z.1 + s • basisVec i, z.2))
        (radialDist z.2 ^ (2 : Nat) * u i - z.2 i * P_u u z) 0 := by
      simpa [Fobs] using hasDerivAt_qPath_F_u u i z
    have hg : HasDerivAt
        (fun s : Real => Uobs (z.1 + s • basisVec i, z.2))
        (u i / radialDist z.1 - X_u u z * z.1 i / (radialDist z.1) ^ (3 : Nat)) 0 := by
      simpa [Uobs] using hasDerivAt_qPath_U_scalar_of_radialDist_ne_zero u i z h
    exact (hf.sub (hg.const_mul (mp.m * gp.mu))).deriv
  have hAp :
      ∀ i : Fin 3,
        partialP (A_u mp gp u) i z =
          (2 * z.2 i * X_u u z - z.1 i * P_u u z - inner ℝ z.1 z.2 * u i) -
            (mp.m * gp.mu) * 0 := by
    intro i
    rw [hA]
    have hf : HasDerivAt
        (fun s : Real => Fobs (z.1, z.2 + s • basisVec i))
        (2 * z.2 i * X_u u z - z.1 i * P_u u z - inner ℝ z.1 z.2 * u i) 0 := by
      simpa [Fobs] using hasDerivAt_pPath_F_u u i z
    have hg : HasDerivAt
        (fun s : Real => Uobs (z.1, z.2 + s • basisVec i))
        0 0 := by
      simpa [Uobs] using hasDerivAt_pPath_U_scalar u i z
    exact (hf.sub (hg.const_mul (mp.m * gp.mu))).deriv
  have hp0 := partialP_keplerHamiltonian mp gp 0 z
  have hp1 := partialP_keplerHamiltonian mp gp 1 z
  have hp2 := partialP_keplerHamiltonian mp gp 2 z
  have hq0 := partialQ_keplerHamiltonian_of_radialDist_ne_zero mp gp 0 z h
  have hq1 := partialQ_keplerHamiltonian_of_radialDist_ne_zero mp gp 1 z h
  have hq2 := partialQ_keplerHamiltonian_of_radialDist_ne_zero mp gp 2 z h
  have hrq2 :
      radialDist z.1 ^ (2 : Nat) = z.1 0 ^ (2 : Nat) + z.1 1 ^ (2 : Nat) + z.1 2 ^ (2 : Nat) := by
    simpa [radialDist, Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.1)
  have hrp2 :
      radialDist z.2 ^ (2 : Nat) = z.2 0 ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
    simpa [radialDist, Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.2)
  unfold poissonBracket
  rw [hAq 0, hAp 0, hAq 1, hAp 1, hAq 2, hAp 2]
  rw [hp0, hp1, hp2, hq0, hq1, hq2, inner_fin3]
  simp [X_u, P_u]
  field_simp [h, ne_of_gt mp.hm]
  rw [hrq2, hrp2]
  ring_nf

theorem poisson_L_u_A_u
    (mp : MassParam) (gp : GravitationalParam)
    (u v : Vec3) (z : PhaseSpace) (h : radialDist z.1 ≠ 0) :
    poissonBracket (L_u u) (A_u mp gp v) z = A_u mp gp (cross u v) z := by
  have hAq0 := partialQ_A_u_of_radialDist_ne_zero_div mp gp v 0 z h
  have hAq1 := partialQ_A_u_of_radialDist_ne_zero_div mp gp v 1 z h
  have hAq2 := partialQ_A_u_of_radialDist_ne_zero_div mp gp v 2 z h
  have hAp0 := partialP_A_u mp gp v 0 z
  have hAp1 := partialP_A_u mp gp v 1 z
  have hAp2 := partialP_A_u mp gp v 2 z
  unfold poissonBracket
  rw [hAq0, hAq1, hAq2, hAp0, hAp1, hAp2]
  rw [A_u_eq_observables]
  simp [partialQ_L_u_0, partialQ_L_u_1, partialQ_L_u_2,
    partialP_L_u_0, partialP_L_u_1, partialP_L_u_2,
    X_u, P_u, cross, cross_apply, inner_fin3, radialDist]
  have hz : ‖z.1‖ ≠ 0 := by simpa [radialDist] using h
  field_simp [hz]
  ring_nf

lemma poissonBracket_skew (F G : PhaseSpace -> Real) (z : PhaseSpace) :
    poissonBracket F G z = -poissonBracket G F z := by
  unfold poissonBracket
  ring

lemma A_u_basis0 (mp : MassParam) (gp : GravitationalParam) :
    A_u mp gp (basisVec 0) = A0 mp gp := by
  funext z
  simp [A_u, basisVec]

lemma A_u_basis1 (mp : MassParam) (gp : GravitationalParam) :
    A_u mp gp (basisVec 1) = A1 mp gp := by
  funext z
  simp [A_u, basisVec]

lemma A_u_basis2 (mp : MassParam) (gp : GravitationalParam) :
    A_u mp gp (basisVec 2) = A2 mp gp := by
  funext z
  simp [A_u, basisVec]

lemma poisson_A0_A1
    (mp : MassParam) (gp : GravitationalParam)
    (z : PhaseSpace) (h : radialDist z.1 ≠ 0) :
    poissonBracket (A0 mp gp) (A1 mp gp) z =
      -2 * mp.m * keplerHamiltonian mp gp z * L2 z := by
  have hq00 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 0) 0 z h
  have hq01 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 0) 1 z h
  have hq02 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 0) 2 z h
  have hp00 := partialP_A_u mp gp (basisVec 0) 0 z
  have hp01 := partialP_A_u mp gp (basisVec 0) 1 z
  have hp02 := partialP_A_u mp gp (basisVec 0) 2 z
  have hq10 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 1) 0 z h
  have hq11 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 1) 1 z h
  have hq12 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 1) 2 z h
  have hp10 := partialP_A_u mp gp (basisVec 1) 0 z
  have hp11 := partialP_A_u mp gp (basisVec 1) 1 z
  have hp12 := partialP_A_u mp gp (basisVec 1) 2 z
  have hz : ‖z.1‖ ≠ 0 := by
    simpa [radialDist] using h
  have hp2 :
      ‖z.2‖ ^ (2 : Nat) = z.2 0 ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
    simpa [Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.2)
  have hq2 :
      ‖z.1‖ ^ (2 : Nat) = z.1 0 ^ (2 : Nat) + z.1 1 ^ (2 : Nat) + z.1 2 ^ (2 : Nat) := by
    simpa [Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.1)
  have hq3 :
      ‖z.1‖ ^ (3 : Nat) =
        (z.1 0 ^ (2 : Nat) + z.1 1 ^ (2 : Nat) + z.1 2 ^ (2 : Nat)) * ‖z.1‖ := by
    calc
      ‖z.1‖ ^ (3 : Nat) = ‖z.1‖ ^ (2 : Nat) * ‖z.1‖ := by ring_nf
      _ = (z.1 0 ^ (2 : Nat) + z.1 1 ^ (2 : Nat) + z.1 2 ^ (2 : Nat)) * ‖z.1‖ := by
            rw [hq2]
  calc
    poissonBracket (A0 mp gp) (A1 mp gp) z =
        poissonBracket (A_u mp gp (basisVec 0)) (A_u mp gp (basisVec 1)) z := by
          rw [A_u_basis0, A_u_basis1]
    _ = -2 * mp.m * keplerHamiltonian mp gp z * L2 z := by
          unfold poissonBracket
          rw [hq00, hq01, hq02, hp00, hp01, hp02, hq10, hq11, hq12, hp10, hp11, hp12]
          simp [basisVec, X_u, P_u, inner_fin3, keplerHamiltonian, energy, radialDist, L2]
          field_simp [hz, ne_of_gt mp.hm]
          rw [hp2, hq2, hq3]
          ring_nf

lemma poisson_A1_A2
    (mp : MassParam) (gp : GravitationalParam)
    (z : PhaseSpace) (h : radialDist z.1 ≠ 0) :
    poissonBracket (A1 mp gp) (A2 mp gp) z =
      -2 * mp.m * keplerHamiltonian mp gp z * L0 z := by
  have hq10 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 1) 0 z h
  have hq11 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 1) 1 z h
  have hq12 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 1) 2 z h
  have hp10 := partialP_A_u mp gp (basisVec 1) 0 z
  have hp11 := partialP_A_u mp gp (basisVec 1) 1 z
  have hp12 := partialP_A_u mp gp (basisVec 1) 2 z
  have hq20 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 2) 0 z h
  have hq21 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 2) 1 z h
  have hq22 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 2) 2 z h
  have hp20 := partialP_A_u mp gp (basisVec 2) 0 z
  have hp21 := partialP_A_u mp gp (basisVec 2) 1 z
  have hp22 := partialP_A_u mp gp (basisVec 2) 2 z
  have hz : ‖z.1‖ ≠ 0 := by
    simpa [radialDist] using h
  have hp2 :
      ‖z.2‖ ^ (2 : Nat) = z.2 0 ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
    simpa [Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.2)
  have hq2 :
      ‖z.1‖ ^ (2 : Nat) = z.1 0 ^ (2 : Nat) + z.1 1 ^ (2 : Nat) + z.1 2 ^ (2 : Nat) := by
    simpa [Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.1)
  have hq3 :
      ‖z.1‖ ^ (3 : Nat) =
        (z.1 0 ^ (2 : Nat) + z.1 1 ^ (2 : Nat) + z.1 2 ^ (2 : Nat)) * ‖z.1‖ := by
    calc
      ‖z.1‖ ^ (3 : Nat) = ‖z.1‖ ^ (2 : Nat) * ‖z.1‖ := by ring_nf
      _ = (z.1 0 ^ (2 : Nat) + z.1 1 ^ (2 : Nat) + z.1 2 ^ (2 : Nat)) * ‖z.1‖ := by
            rw [hq2]
  calc
    poissonBracket (A1 mp gp) (A2 mp gp) z =
        poissonBracket (A_u mp gp (basisVec 1)) (A_u mp gp (basisVec 2)) z := by
          rw [A_u_basis1, A_u_basis2]
    _ = -2 * mp.m * keplerHamiltonian mp gp z * L0 z := by
          unfold poissonBracket
          rw [hq10, hq11, hq12, hp10, hp11, hp12, hq20, hq21, hq22, hp20, hp21, hp22]
          simp [basisVec, X_u, P_u, inner_fin3, keplerHamiltonian, energy, radialDist, L0]
          field_simp [hz, ne_of_gt mp.hm]
          rw [hp2, hq2, hq3]
          ring_nf

lemma poisson_A2_A0
    (mp : MassParam) (gp : GravitationalParam)
    (z : PhaseSpace) (h : radialDist z.1 ≠ 0) :
    poissonBracket (A2 mp gp) (A0 mp gp) z =
      -2 * mp.m * keplerHamiltonian mp gp z * L1 z := by
  have hq20 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 2) 0 z h
  have hq21 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 2) 1 z h
  have hq22 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 2) 2 z h
  have hp20 := partialP_A_u mp gp (basisVec 2) 0 z
  have hp21 := partialP_A_u mp gp (basisVec 2) 1 z
  have hp22 := partialP_A_u mp gp (basisVec 2) 2 z
  have hq00 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 0) 0 z h
  have hq01 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 0) 1 z h
  have hq02 := partialQ_A_u_of_radialDist_ne_zero_div mp gp (basisVec 0) 2 z h
  have hp00 := partialP_A_u mp gp (basisVec 0) 0 z
  have hp01 := partialP_A_u mp gp (basisVec 0) 1 z
  have hp02 := partialP_A_u mp gp (basisVec 0) 2 z
  have hz : ‖z.1‖ ≠ 0 := by
    simpa [radialDist] using h
  have hp2 :
      ‖z.2‖ ^ (2 : Nat) = z.2 0 ^ (2 : Nat) + z.2 1 ^ (2 : Nat) + z.2 2 ^ (2 : Nat) := by
    simpa [Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.2)
  have hq2 :
      ‖z.1‖ ^ (2 : Nat) = z.1 0 ^ (2 : Nat) + z.1 1 ^ (2 : Nat) + z.1 2 ^ (2 : Nat) := by
    simpa [Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq (n := Fin 3) z.1)
  have hq3 :
      ‖z.1‖ ^ (3 : Nat) =
        (z.1 0 ^ (2 : Nat) + z.1 1 ^ (2 : Nat) + z.1 2 ^ (2 : Nat)) * ‖z.1‖ := by
    calc
      ‖z.1‖ ^ (3 : Nat) = ‖z.1‖ ^ (2 : Nat) * ‖z.1‖ := by ring_nf
      _ = (z.1 0 ^ (2 : Nat) + z.1 1 ^ (2 : Nat) + z.1 2 ^ (2 : Nat)) * ‖z.1‖ := by
            rw [hq2]
  calc
    poissonBracket (A2 mp gp) (A0 mp gp) z =
        poissonBracket (A_u mp gp (basisVec 2)) (A_u mp gp (basisVec 0)) z := by
          rw [A_u_basis2, A_u_basis0]
    _ = -2 * mp.m * keplerHamiltonian mp gp z * L1 z := by
          unfold poissonBracket
          rw [hq20, hq21, hq22, hp20, hp21, hp22, hq00, hq01, hq02, hp00, hp01, hp02]
          simp [basisVec, X_u, P_u, inner_fin3, keplerHamiltonian, energy, radialDist, L1]
          field_simp [hz, ne_of_gt mp.hm]
          rw [hp2, hq2, hq3]
          ring_nf

lemma poisson_A_u_add_left
    (mp : MassParam) (gp : GravitationalParam)
    (u v w : Vec3) (z : PhaseSpace) (h : radialDist z.1 ≠ 0) :
    poissonBracket (A_u mp gp (u + v)) (A_u mp gp w) z =
      poissonBracket (A_u mp gp u) (A_u mp gp w) z +
        poissonBracket (A_u mp gp v) (A_u mp gp w) z := by
  have hqsum0 :
      partialQ (A_u mp gp (u + v)) 0 z =
        partialQ (A_u mp gp u) 0 z + partialQ (A_u mp gp v) 0 z := by
    rw [partialQ_A_u_of_radialDist_ne_zero_div mp gp (u + v) 0 z h,
      partialQ_A_u_of_radialDist_ne_zero_div mp gp u 0 z h,
      partialQ_A_u_of_radialDist_ne_zero_div mp gp v 0 z h]
    simp [X_u, P_u, inner_fin3]
    ring
  have hqsum1 :
      partialQ (A_u mp gp (u + v)) 1 z =
        partialQ (A_u mp gp u) 1 z + partialQ (A_u mp gp v) 1 z := by
    rw [partialQ_A_u_of_radialDist_ne_zero_div mp gp (u + v) 1 z h,
      partialQ_A_u_of_radialDist_ne_zero_div mp gp u 1 z h,
      partialQ_A_u_of_radialDist_ne_zero_div mp gp v 1 z h]
    simp [X_u, P_u, inner_fin3]
    ring
  have hqsum2 :
      partialQ (A_u mp gp (u + v)) 2 z =
        partialQ (A_u mp gp u) 2 z + partialQ (A_u mp gp v) 2 z := by
    rw [partialQ_A_u_of_radialDist_ne_zero_div mp gp (u + v) 2 z h,
      partialQ_A_u_of_radialDist_ne_zero_div mp gp u 2 z h,
      partialQ_A_u_of_radialDist_ne_zero_div mp gp v 2 z h]
    simp [X_u, P_u, inner_fin3]
    ring
  have hpsum0 :
      partialP (A_u mp gp (u + v)) 0 z =
        partialP (A_u mp gp u) 0 z + partialP (A_u mp gp v) 0 z := by
    rw [partialP_A_u mp gp (u + v) 0 z, partialP_A_u mp gp u 0 z, partialP_A_u mp gp v 0 z]
    simp [X_u, P_u, inner_fin3]
    ring
  have hpsum1 :
      partialP (A_u mp gp (u + v)) 1 z =
        partialP (A_u mp gp u) 1 z + partialP (A_u mp gp v) 1 z := by
    rw [partialP_A_u mp gp (u + v) 1 z, partialP_A_u mp gp u 1 z, partialP_A_u mp gp v 1 z]
    simp [X_u, P_u, inner_fin3]
    ring
  have hpsum2 :
      partialP (A_u mp gp (u + v)) 2 z =
        partialP (A_u mp gp u) 2 z + partialP (A_u mp gp v) 2 z := by
    rw [partialP_A_u mp gp (u + v) 2 z, partialP_A_u mp gp u 2 z, partialP_A_u mp gp v 2 z]
    simp [X_u, P_u, inner_fin3]
    ring
  unfold poissonBracket
  rw [hqsum0, hqsum1, hqsum2, hpsum0, hpsum1, hpsum2]
  ring

lemma poisson_A_u_add_right
    (mp : MassParam) (gp : GravitationalParam)
    (u v w : Vec3) (z : PhaseSpace) (h : radialDist z.1 ≠ 0) :
    poissonBracket (A_u mp gp u) (A_u mp gp (v + w)) z =
      poissonBracket (A_u mp gp u) (A_u mp gp v) z +
        poissonBracket (A_u mp gp u) (A_u mp gp w) z := by
  have huv := poisson_A_u_add_left mp gp (u := v) (v := w) (w := u) z h
  have hvu :
      -poissonBracket (A_u mp gp v) (A_u mp gp u) z =
        poissonBracket (A_u mp gp u) (A_u mp gp v) z := by
    have hsk := poissonBracket_skew (A_u mp gp v) (A_u mp gp u) z
    linarith
  have hwu :
      -poissonBracket (A_u mp gp w) (A_u mp gp u) z =
        poissonBracket (A_u mp gp u) (A_u mp gp w) z := by
    have hsk := poissonBracket_skew (A_u mp gp w) (A_u mp gp u) z
    linarith
  calc
    poissonBracket (A_u mp gp u) (A_u mp gp (v + w)) z
        = -poissonBracket (A_u mp gp (v + w)) (A_u mp gp u) z := by
            rw [poissonBracket_skew]
    _ = -(poissonBracket (A_u mp gp v) (A_u mp gp u) z +
          poissonBracket (A_u mp gp w) (A_u mp gp u) z) := by
            rw [huv]
    _ = -poissonBracket (A_u mp gp v) (A_u mp gp u) z +
          -poissonBracket (A_u mp gp w) (A_u mp gp u) z := by
            ring
    _ = poissonBracket (A_u mp gp u) (A_u mp gp v) z +
          poissonBracket (A_u mp gp u) (A_u mp gp w) z := by
            rw [hvu, hwu]

lemma poisson_A_u_smul_left
    (mp : MassParam) (gp : GravitationalParam)
    (a : Real) (u v : Vec3) (z : PhaseSpace) (h : radialDist z.1 ≠ 0) :
    poissonBracket (A_u mp gp (a • u)) (A_u mp gp v) z =
      a * poissonBracket (A_u mp gp u) (A_u mp gp v) z := by
  have hqau0 :
      partialQ (A_u mp gp (a • u)) 0 z = a * partialQ (A_u mp gp u) 0 z := by
    rw [partialQ_A_u_of_radialDist_ne_zero_div mp gp (a • u) 0 z h,
      partialQ_A_u_of_radialDist_ne_zero_div mp gp u 0 z h]
    simp [X_u, P_u, inner_fin3]
    ring
  have hqau1 :
      partialQ (A_u mp gp (a • u)) 1 z = a * partialQ (A_u mp gp u) 1 z := by
    rw [partialQ_A_u_of_radialDist_ne_zero_div mp gp (a • u) 1 z h,
      partialQ_A_u_of_radialDist_ne_zero_div mp gp u 1 z h]
    simp [X_u, P_u, inner_fin3]
    ring
  have hqau2 :
      partialQ (A_u mp gp (a • u)) 2 z = a * partialQ (A_u mp gp u) 2 z := by
    rw [partialQ_A_u_of_radialDist_ne_zero_div mp gp (a • u) 2 z h,
      partialQ_A_u_of_radialDist_ne_zero_div mp gp u 2 z h]
    simp [X_u, P_u, inner_fin3]
    ring
  have hpau0 :
      partialP (A_u mp gp (a • u)) 0 z = a * partialP (A_u mp gp u) 0 z := by
    rw [partialP_A_u mp gp (a • u) 0 z, partialP_A_u mp gp u 0 z]
    simp [X_u, P_u, inner_fin3]
    ring
  have hpau1 :
      partialP (A_u mp gp (a • u)) 1 z = a * partialP (A_u mp gp u) 1 z := by
    rw [partialP_A_u mp gp (a • u) 1 z, partialP_A_u mp gp u 1 z]
    simp [X_u, P_u, inner_fin3]
    ring
  have hpau2 :
      partialP (A_u mp gp (a • u)) 2 z = a * partialP (A_u mp gp u) 2 z := by
    rw [partialP_A_u mp gp (a • u) 2 z, partialP_A_u mp gp u 2 z]
    simp [X_u, P_u, inner_fin3]
    ring
  unfold poissonBracket
  rw [hqau0, hqau1, hqau2, hpau0, hpau1, hpau2]
  ring

lemma poisson_A_u_smul_right
    (mp : MassParam) (gp : GravitationalParam)
    (a : Real) (u v : Vec3) (z : PhaseSpace) (h : radialDist z.1 ≠ 0) :
    poissonBracket (A_u mp gp u) (A_u mp gp (a • v)) z =
      a * poissonBracket (A_u mp gp u) (A_u mp gp v) z := by
  have hvu :
      -poissonBracket (A_u mp gp v) (A_u mp gp u) z =
        poissonBracket (A_u mp gp u) (A_u mp gp v) z := by
    have hsk := poissonBracket_skew (A_u mp gp v) (A_u mp gp u) z
    linarith
  calc
    poissonBracket (A_u mp gp u) (A_u mp gp (a • v)) z
        = -poissonBracket (A_u mp gp (a • v)) (A_u mp gp u) z := by
            rw [poissonBracket_skew]
    _ = -(a * poissonBracket (A_u mp gp v) (A_u mp gp u) z) := by
            rw [poisson_A_u_smul_left mp gp a v u z h]
    _ = a * (-poissonBracket (A_u mp gp v) (A_u mp gp u) z) := by
            ring
    _ = a * poissonBracket (A_u mp gp u) (A_u mp gp v) z := by
            rw [hvu]

theorem poisson_A_u_A_u
    (mp : MassParam) (gp : GravitationalParam)
    (u v : Vec3) (z : PhaseSpace) (h : radialDist z.1 ≠ 0) :
    poissonBracket (A_u mp gp u) (A_u mp gp v) z =
      -2 * mp.m * keplerHamiltonian mp gp z * L_u (cross u v) z := by
  let e0 := basisVec 0
  let e1 := basisVec 1
  let e2 := basisVec 2
  have hu :
      u = (u 0) • e0 + ((u 1) • e1 + (u 2) • e2) := by
    ext i
    fin_cases i <;> simp [e0, e1, e2, basisVec]
  have hv :
      v = (v 0) • e0 + ((v 1) • e1 + (v 2) • e2) := by
    ext i
    fin_cases i <;> simp [e0, e1, e2, basisVec]
  have h00 : poissonBracket (A0 mp gp) (A0 mp gp) z = 0 := by
    have hsk := poissonBracket_skew (A0 mp gp) (A0 mp gp) z
    linarith
  have h11 : poissonBracket (A1 mp gp) (A1 mp gp) z = 0 := by
    have hsk := poissonBracket_skew (A1 mp gp) (A1 mp gp) z
    linarith
  have h22 : poissonBracket (A2 mp gp) (A2 mp gp) z = 0 := by
    have hsk := poissonBracket_skew (A2 mp gp) (A2 mp gp) z
    linarith
  have h01 := poisson_A0_A1 mp gp z h
  have h12 := poisson_A1_A2 mp gp z h
  have h20 := poisson_A2_A0 mp gp z h
  have h10 :
      poissonBracket (A1 mp gp) (A0 mp gp) z =
        2 * mp.m * keplerHamiltonian mp gp z * L2 z := by
    calc
      poissonBracket (A1 mp gp) (A0 mp gp) z
          = -poissonBracket (A0 mp gp) (A1 mp gp) z := by
              rw [poissonBracket_skew]
      _ = -(-2 * mp.m * keplerHamiltonian mp gp z * L2 z) := by rw [h01]
      _ = 2 * mp.m * keplerHamiltonian mp gp z * L2 z := by ring
  have h21 :
      poissonBracket (A2 mp gp) (A1 mp gp) z =
        2 * mp.m * keplerHamiltonian mp gp z * L0 z := by
    calc
      poissonBracket (A2 mp gp) (A1 mp gp) z
          = -poissonBracket (A1 mp gp) (A2 mp gp) z := by
              rw [poissonBracket_skew]
      _ = -(-2 * mp.m * keplerHamiltonian mp gp z * L0 z) := by rw [h12]
      _ = 2 * mp.m * keplerHamiltonian mp gp z * L0 z := by ring
  have h02 :
      poissonBracket (A0 mp gp) (A2 mp gp) z =
        2 * mp.m * keplerHamiltonian mp gp z * L1 z := by
    calc
      poissonBracket (A0 mp gp) (A2 mp gp) z
          = -poissonBracket (A2 mp gp) (A0 mp gp) z := by
              rw [poissonBracket_skew]
      _ = -(-2 * mp.m * keplerHamiltonian mp gp z * L1 z) := by rw [h20]
      _ = 2 * mp.m * keplerHamiltonian mp gp z * L1 z := by ring
  rw [hu, hv]
  simp_rw [poisson_A_u_add_left (mp := mp) (gp := gp) (z := z) (h := h),
    poisson_A_u_add_right (mp := mp) (gp := gp) (z := z) (h := h),
    poisson_A_u_smul_left (mp := mp) (gp := gp) (z := z) (h := h),
    poisson_A_u_smul_right (mp := mp) (gp := gp) (z := z) (h := h)]
  simp_rw [e0, e1, e2, A_u_basis0, A_u_basis1, A_u_basis2]
  rw [h00, h11, h22, h01, h10, h12, h21, h20, h02]
  simp [e0, e1, e2, basisVec, L_u, cross, cross_apply]
  ring_nf

def K_u (mp : MassParam) (gp : GravitationalParam) (h : Real) (u : Vec3) : PhaseSpace -> Real :=
  A_u mp gp ((1 / Real.sqrt (-2 * mp.m * h)) • u)

lemma hidden_scale_sq_mul (mp : MassParam) {h : Real} (hh : h < 0) :
    ((1 / Real.sqrt (-2 * mp.m * h)) ^ (2 : Nat)) * (-2 * mp.m * h) = 1 := by
  have hpos : 0 < -(2 * mp.m * h) := by
    nlinarith [mp.hm, hh]
  have hsqrt_ne : Real.sqrt (-(2 * mp.m * h)) ≠ 0 := by
    exact Real.sqrt_ne_zero'.2 hpos
  have hsqrt_sq : Real.sqrt (-(2 * mp.m * h)) ^ (2 : Nat) = -(2 * mp.m * h) := by
    rw [Real.sq_sqrt (le_of_lt hpos)]
  have hsqrt_eq : Real.sqrt (-2 * mp.m * h) = Real.sqrt (-(2 * mp.m * h)) := by
    congr 1
    ring
  rw [hsqrt_eq]
  rw [pow_two]
  field_simp [hsqrt_ne]
  rw [hsqrt_sq]

theorem poisson_L_u_K_u
    (mp : MassParam) (gp : GravitationalParam) (h : Real)
    (u v : Vec3) (z : PhaseSpace) (hr : radialDist z.1 ≠ 0) :
    poissonBracket (L_u u) (K_u mp gp h v) z =
      K_u mp gp h (cross u v) z := by
  let c : Real := 1 / Real.sqrt (-2 * mp.m * h)
  have hcross : cross u (c • v) = c • cross u v := by
    ext i
    fin_cases i <;> simp [c, cross, cross_apply]
    · ring
    · ring
    · ring
  calc
    poissonBracket (L_u u) (K_u mp gp h v) z
        = poissonBracket (L_u u) (A_u mp gp (c • v)) z := by
            simp [K_u, c]
    _ = A_u mp gp (cross u (c • v)) z := poisson_L_u_A_u mp gp u (c • v) z hr
    _ = A_u mp gp (c • cross u v) z := by rw [hcross]
    _ = K_u mp gp h (cross u v) z := by simp [K_u, c]

theorem poisson_K_u_K_u
    (mp : MassParam) (gp : GravitationalParam) (h : Real)
    (u v : Vec3) (z : PhaseSpace)
    (hz : keplerHamiltonian mp gp z = h) (hh : h < 0) (hr : radialDist z.1 ≠ 0) :
    poissonBracket (K_u mp gp h u) (K_u mp gp h v) z =
      L_u (cross u v) z := by
  let c : Real := 1 / Real.sqrt (-2 * mp.m * h)
  have hcross :
      cross (c • u) (c • v) = (c ^ (2 : Nat)) • cross u v := by
    ext i
    fin_cases i <;> simp [c, pow_two, cross, cross_apply]
    · ring
    · ring
    · ring
  have hLsmul :
      L_u ((c ^ (2 : Nat)) • cross u v) z = (c ^ (2 : Nat)) * L_u (cross u v) z := by
    simp [L_u]
    ring
  have hcoeff : -2 * mp.m * h * c ^ (2 : Nat) = 1 := by
    calc
      -2 * mp.m * h * c ^ (2 : Nat)
          = (c ^ (2 : Nat)) * (-2 * mp.m * h) := by ring
      _ = 1 := by
            simpa [c] using hidden_scale_sq_mul mp hh
  calc
    poissonBracket (K_u mp gp h u) (K_u mp gp h v) z
        = poissonBracket (A_u mp gp (c • u)) (A_u mp gp (c • v)) z := by
            simp [K_u, c]
    _ = -2 * mp.m * keplerHamiltonian mp gp z * L_u (cross (c • u) (c • v)) z := by
          exact poisson_A_u_A_u mp gp (c • u) (c • v) z hr
    _ = -2 * mp.m * h * L_u ((c ^ (2 : Nat)) • cross u v) z := by rw [hz, hcross]
    _ = (-2 * mp.m * h * c ^ (2 : Nat)) * L_u (cross u v) z := by
          rw [hLsmul]
          ring
    _ = L_u (cross u v) z := by rw [hcoeff, one_mul]

def NegativeEnergyShell (mp : MassParam) (gp : GravitationalParam) (h : Real) :=
  { z : PhaseSpace // keplerHamiltonian mp gp z = h ∧ radialDist z.1 ≠ 0 }

def so4ModelBracket (a b : Vec3 × Vec3) : Vec3 × Vec3 :=
  (cross a.1 b.1 + cross a.2 b.2, cross a.1 b.2 + cross a.2 b.1)

def PhiMatrix (uv : Vec3 × Vec3) : Matrix (Fin 4) (Fin 4) Real :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 0
    | 0, 1 => -(uv.1 2)
    | 0, 2 => uv.1 1
    | 0, 3 => uv.2 0
    | 1, 0 => uv.1 2
    | 1, 1 => 0
    | 1, 2 => -(uv.1 0)
    | 1, 3 => uv.2 1
    | 2, 0 => -(uv.1 1)
    | 2, 1 => uv.1 0
    | 2, 2 => 0
    | 2, 3 => uv.2 2
    | 3, 0 => -(uv.2 0)
    | 3, 1 => -(uv.2 1)
    | 3, 2 => -(uv.2 2)
    | 3, 3 => 0
    | _, _ => 0

lemma PhiMatrix_mem_so (uv : Vec3 × Vec3) :
    PhiMatrix uv ∈ LieAlgebra.Orthogonal.so (Fin 4) Real := by
  rw [LieAlgebra.Orthogonal.mem_so]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [PhiMatrix, Matrix.transpose_apply]

def Phi : (Vec3 × Vec3) →ₗ[ℝ] LieAlgebra.Orthogonal.so (Fin 4) Real where
  toFun := fun uv => ⟨PhiMatrix uv, PhiMatrix_mem_so uv⟩
  map_add' := by
    intro a b
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [PhiMatrix] <;> ring
  map_smul' := by
    intro c a
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [PhiMatrix] <;> ring

lemma Phi_injective : Function.Injective Phi := by
  intro a b hab
  apply Prod.ext <;> ext i <;> fin_cases i
  · have h := congrArg (fun M : LieAlgebra.Orthogonal.so (Fin 4) Real => (M : Matrix (Fin 4) (Fin 4) Real) 2 1) hab
    simpa [Phi, PhiMatrix] using h
  · have h := congrArg (fun M : LieAlgebra.Orthogonal.so (Fin 4) Real => (M : Matrix (Fin 4) (Fin 4) Real) 0 2) hab
    simpa [Phi, PhiMatrix] using h
  · have h := congrArg (fun M : LieAlgebra.Orthogonal.so (Fin 4) Real => (M : Matrix (Fin 4) (Fin 4) Real) 1 0) hab
    simpa [Phi, PhiMatrix] using h
  · have h := congrArg (fun M : LieAlgebra.Orthogonal.so (Fin 4) Real => (M : Matrix (Fin 4) (Fin 4) Real) 0 3) hab
    simpa [Phi, PhiMatrix] using h
  · have h := congrArg (fun M : LieAlgebra.Orthogonal.so (Fin 4) Real => (M : Matrix (Fin 4) (Fin 4) Real) 1 3) hab
    simpa [Phi, PhiMatrix] using h
  · have h := congrArg (fun M : LieAlgebra.Orthogonal.so (Fin 4) Real => (M : Matrix (Fin 4) (Fin 4) Real) 2 3) hab
    simpa [Phi, PhiMatrix] using h

lemma so4_entry_skew (M : LieAlgebra.Orthogonal.so (Fin 4) Real) (i j : Fin 4) :
    (M : Matrix (Fin 4) (Fin 4) Real) i j = - (M : Matrix (Fin 4) (Fin 4) Real) j i := by
  have hskew :=
    (LieAlgebra.Orthogonal.mem_so (A := (M : Matrix (Fin 4) (Fin 4) Real))).1 M.2
  have h := congrFun (congrFun hskew j) i
  simpa [Matrix.transpose_apply] using h

lemma so4_diag_zero (M : LieAlgebra.Orthogonal.so (Fin 4) Real) (i : Fin 4) :
    (M : Matrix (Fin 4) (Fin 4) Real) i i = 0 := by
  have h := so4_entry_skew M i i
  nlinarith

lemma Phi_surjective : Function.Surjective Phi := by
  intro M
  let u : Vec3 := ((M : Matrix (Fin 4) (Fin 4) Real) 2 1) • basisVec 0 +
    ((M : Matrix (Fin 4) (Fin 4) Real) 0 2) • basisVec 1 +
    ((M : Matrix (Fin 4) (Fin 4) Real) 1 0) • basisVec 2
  let v : Vec3 := ((M : Matrix (Fin 4) (Fin 4) Real) 0 3) • basisVec 0 +
    ((M : Matrix (Fin 4) (Fin 4) Real) 1 3) • basisVec 1 +
    ((M : Matrix (Fin 4) (Fin 4) Real) 2 3) • basisVec 2
  refine ⟨(u, v), ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · symm
    simpa [Phi, PhiMatrix, u, v, basisVec] using so4_diag_zero M 0
  · simpa [Phi, PhiMatrix, u, v, basisVec] using (so4_entry_skew M 0 1).symm
  · simp [Phi, PhiMatrix, u, v, basisVec]
  · simp [Phi, PhiMatrix, u, v, basisVec]
  · simp [Phi, PhiMatrix, u, v, basisVec]
  · symm
    simpa [Phi, PhiMatrix, u, v, basisVec] using so4_diag_zero M 1
  · simpa [Phi, PhiMatrix, u, v, basisVec] using (so4_entry_skew M 1 2).symm
  · simp [Phi, PhiMatrix, u, v, basisVec]
  · simpa [Phi, PhiMatrix, u, v, basisVec] using (so4_entry_skew M 2 0).symm
  · simp [Phi, PhiMatrix, u, v, basisVec]
  · symm
    simpa [Phi, PhiMatrix, u, v, basisVec] using so4_diag_zero M 2
  · simp [Phi, PhiMatrix, u, v, basisVec]
  · simpa [Phi, PhiMatrix, u, v, basisVec] using (so4_entry_skew M 3 0).symm
  · simpa [Phi, PhiMatrix, u, v, basisVec] using (so4_entry_skew M 3 1).symm
  · simpa [Phi, PhiMatrix, u, v, basisVec] using (so4_entry_skew M 3 2).symm
  · symm
    simpa [Phi, PhiMatrix, u, v, basisVec] using so4_diag_zero M 3

lemma PhiMatrix_bracket (a b : Vec3 × Vec3) :
    PhiMatrix (so4ModelBracket a b) = PhiMatrix a * PhiMatrix b - PhiMatrix b * PhiMatrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PhiMatrix, so4ModelBracket, cross, cross_apply, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

theorem so4_model_isomorphic_to_so4 :
    Function.Bijective Phi ∧
    ∀ a b : Vec3 × Vec3,
      (Phi (so4ModelBracket a b) : Matrix (Fin 4) (Fin 4) Real) =
        (Phi a : Matrix (Fin 4) (Fin 4) Real) * (Phi b : Matrix (Fin 4) (Fin 4) Real) -
          (Phi b : Matrix (Fin 4) (Fin 4) Real) * (Phi a : Matrix (Fin 4) (Fin 4) Real) := by
  refine ⟨⟨Phi_injective, Phi_surjective⟩, ?_⟩
  intro a b
  simpa [Phi] using PhiMatrix_bracket a b

def mu_h (mp : MassParam) (gp : GravitationalParam) (h : Real) (uv : Vec3 × Vec3) :
    PhaseSpace -> Real :=
  fun z => L_u uv.1 z + K_u mp gp h uv.2 z

lemma L_u_add (u v : Vec3) :
    L_u (u + v) = fun z : PhaseSpace => L_u u z + L_u v z := by
  funext z
  simp [L_u]
  ring

lemma K_u_add (mp : MassParam) (gp : GravitationalParam) (h : Real) (u v : Vec3) :
    K_u mp gp h (u + v) = fun z : PhaseSpace => K_u mp gp h u z + K_u mp gp h v z := by
  funext z
  simp [K_u, A_u]
  ring

lemma mu_h_zero (mp : MassParam) (gp : GravitationalParam) (h : Real) :
    mu_h mp gp h (0, 0) = 0 := by
  funext z
  simp [mu_h, L_u, K_u, A_u]

set_option linter.flexible false in
lemma hasDerivAt_qPath_L_u_0 (u : Vec3) (z : PhaseSpace) :
    HasDerivAt (fun s : Real => L_u u (z.1 + s • basisVec 0, z.2))
      (-(u 1) * z.2 2 + (u 2) * z.2 1) 0 := by
  unfold L_u
  simp [L0, L1, L2, basisVec]
  have hfun :
      (fun s : Real =>
        u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
          u 1 * (z.1 2 * z.2 0 - (z.1 0 + s) * z.2 2) +
          u 2 * ((z.1 0 + s) * z.2 1 - z.1 1 * z.2 0)) =
        fun s : Real =>
          (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
            u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
            u 2 * (z.1 0 * z.2 1 - z.1 1 * z.2 0)) +
          s * (-(u 1) * z.2 2 + (u 2) * z.2 1) := by
    funext s
    ring
  rw [hfun]
  simpa [sub_eq_add_neg] using
    hasDerivAt_const_add_mul_zero
      (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
        u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
        u 2 * (z.1 0 * z.2 1 - z.1 1 * z.2 0))
      (-(u 1) * z.2 2 + (u 2) * z.2 1)

set_option linter.flexible false in
lemma hasDerivAt_qPath_L_u_1 (u : Vec3) (z : PhaseSpace) :
    HasDerivAt (fun s : Real => L_u u (z.1 + s • basisVec 1, z.2))
      (-(u 2) * z.2 0 + (u 0) * z.2 2) 0 := by
  unfold L_u
  simp [L0, L1, L2, basisVec]
  have hfun :
      (fun s : Real =>
        u 0 * ((z.1 1 + s) * z.2 2 - z.1 2 * z.2 1) +
          u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
          u 2 * (z.1 0 * z.2 1 - (z.1 1 + s) * z.2 0)) =
        fun s : Real =>
          (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
            u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
            u 2 * (z.1 0 * z.2 1 - z.1 1 * z.2 0)) +
          s * (-(u 2) * z.2 0 + (u 0) * z.2 2) := by
    funext s
    ring
  rw [hfun]
  simpa [sub_eq_add_neg] using
    hasDerivAt_const_add_mul_zero
      (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
        u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
        u 2 * (z.1 0 * z.2 1 - z.1 1 * z.2 0))
      (-(u 2) * z.2 0 + (u 0) * z.2 2)

set_option linter.flexible false in
lemma hasDerivAt_qPath_L_u_2 (u : Vec3) (z : PhaseSpace) :
    HasDerivAt (fun s : Real => L_u u (z.1 + s • basisVec 2, z.2))
      (-(u 0) * z.2 1 + (u 1) * z.2 0) 0 := by
  unfold L_u
  simp [L0, L1, L2, basisVec]
  have hfun :
      (fun s : Real =>
        u 0 * (z.1 1 * z.2 2 - (z.1 2 + s) * z.2 1) +
          u 1 * ((z.1 2 + s) * z.2 0 - z.1 0 * z.2 2)) =
        fun s : Real =>
          (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
            u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2)) +
          s * (-(u 0) * z.2 1 + (u 1) * z.2 0) := by
    funext s
    ring
  rw [hfun]
  simpa [sub_eq_add_neg] using
    hasDerivAt_const_add_mul_zero
      (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
        u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2))
      (-(u 0) * z.2 1 + (u 1) * z.2 0)

set_option linter.flexible false in
lemma hasDerivAt_pPath_L_u_0 (u : Vec3) (z : PhaseSpace) :
    HasDerivAt (fun s : Real => L_u u (z.1, z.2 + s • basisVec 0))
      ((u 1) * z.1 2 - (u 2) * z.1 1) 0 := by
  unfold L_u
  simp [L0, L1, L2, basisVec]
  have hfun :
      (fun s : Real =>
        u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
          u 1 * (z.1 2 * (z.2 0 + s) - z.1 0 * z.2 2) +
          u 2 * (z.1 0 * z.2 1 - z.1 1 * (z.2 0 + s))) =
        fun s : Real =>
          (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
            u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
            u 2 * (z.1 0 * z.2 1 - z.1 1 * z.2 0)) +
          s * ((u 1) * z.1 2 - (u 2) * z.1 1) := by
    funext s
    ring
  rw [hfun]
  exact
    hasDerivAt_const_add_mul_zero
      (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
        u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
        u 2 * (z.1 0 * z.2 1 - z.1 1 * z.2 0))
      ((u 1) * z.1 2 - (u 2) * z.1 1)

set_option linter.flexible false in
lemma hasDerivAt_pPath_L_u_1 (u : Vec3) (z : PhaseSpace) :
    HasDerivAt (fun s : Real => L_u u (z.1, z.2 + s • basisVec 1))
      ((u 2) * z.1 0 - (u 0) * z.1 2) 0 := by
  unfold L_u
  simp [L0, L1, L2, basisVec]
  have hfun :
      (fun s : Real =>
        u 0 * (z.1 1 * z.2 2 - z.1 2 * (z.2 1 + s)) +
          u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
          u 2 * (z.1 0 * (z.2 1 + s) - z.1 1 * z.2 0)) =
        fun s : Real =>
          (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
            u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
            u 2 * (z.1 0 * z.2 1 - z.1 1 * z.2 0)) +
          s * ((u 2) * z.1 0 - (u 0) * z.1 2) := by
    funext s
    ring
  rw [hfun]
  exact
    hasDerivAt_const_add_mul_zero
      (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
        u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2) +
        u 2 * (z.1 0 * z.2 1 - z.1 1 * z.2 0))
      ((u 2) * z.1 0 - (u 0) * z.1 2)

set_option linter.flexible false in
lemma hasDerivAt_pPath_L_u_2 (u : Vec3) (z : PhaseSpace) :
    HasDerivAt (fun s : Real => L_u u (z.1, z.2 + s • basisVec 2))
      ((u 0) * z.1 1 - (u 1) * z.1 0) 0 := by
  unfold L_u
  simp [L0, L1, L2, basisVec]
  have hfun :
      (fun s : Real =>
        u 0 * (z.1 1 * (z.2 2 + s) - z.1 2 * z.2 1) +
          u 1 * (z.1 2 * z.2 0 - z.1 0 * (z.2 2 + s))) =
        fun s : Real =>
          (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
            u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2)) +
          s * ((u 0) * z.1 1 - (u 1) * z.1 0) := by
    funext s
    ring
  rw [hfun]
  exact
    hasDerivAt_const_add_mul_zero
      (u 0 * (z.1 1 * z.2 2 - z.1 2 * z.2 1) +
        u 1 * (z.1 2 * z.2 0 - z.1 0 * z.2 2))
      ((u 0) * z.1 1 - (u 1) * z.1 0)

lemma hasDerivAt_qPath_L_u (u : Vec3) (i : Fin 3) (z : PhaseSpace) :
    HasDerivAt (fun s : Real => L_u u (z.1 + s • basisVec i, z.2))
      (partialQ (L_u u) i z) 0 := by
  fin_cases i
  · simpa [partialQ_L_u_0] using hasDerivAt_qPath_L_u_0 u z
  · simpa [partialQ_L_u_1] using hasDerivAt_qPath_L_u_1 u z
  · simpa [partialQ_L_u_2] using hasDerivAt_qPath_L_u_2 u z

lemma hasDerivAt_pPath_L_u (u : Vec3) (i : Fin 3) (z : PhaseSpace) :
    HasDerivAt (fun s : Real => L_u u (z.1, z.2 + s • basisVec i))
      (partialP (L_u u) i z) 0 := by
  fin_cases i
  · simpa [partialP_L_u_0] using hasDerivAt_pPath_L_u_0 u z
  · simpa [partialP_L_u_1] using hasDerivAt_pPath_L_u_1 u z
  · simpa [partialP_L_u_2] using hasDerivAt_pPath_L_u_2 u z

lemma hasDerivAt_qPath_A_u_of_radialDist_ne_zero
    (mp : MassParam) (gp : GravitationalParam) (u : Vec3) (i : Fin 3) (z : PhaseSpace)
    (h : radialDist z.1 ≠ 0) :
    HasDerivAt (fun s : Real => A_u mp gp u (z.1 + s • basisVec i, z.2))
      (partialQ (A_u mp gp u) i z) 0 := by
  have hf : HasDerivAt
      (fun s : Real =>
        (fun z : PhaseSpace => radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
          (z.1 + s • basisVec i, z.2))
      (radialDist z.2 ^ (2 : Nat) * u i - z.2 i * P_u u z) 0 := by
    simpa using hasDerivAt_qPath_F_u u i z
  have hg : HasDerivAt
      (fun s : Real => X_u u (z.1 + s • basisVec i, z.2) / radialDist (z.1 + s • basisVec i))
      (u i / radialDist z.1 - X_u u z * z.1 i / (radialDist z.1) ^ (3 : Nat)) 0 := by
    simpa using hasDerivAt_qPath_U_scalar_of_radialDist_ne_zero u i z h
  convert (hf.sub (hg.const_mul (mp.m * gp.mu))) using 1
  · funext s
    simp [A_u_eq_observables, div_eq_mul_inv]
  · simpa using partialQ_A_u_of_radialDist_ne_zero mp gp u i z h

lemma hasDerivAt_pPath_A_u
    (mp : MassParam) (gp : GravitationalParam) (u : Vec3) (i : Fin 3) (z : PhaseSpace) :
    HasDerivAt (fun s : Real => A_u mp gp u (z.1, z.2 + s • basisVec i))
      (partialP (A_u mp gp u) i z) 0 := by
  have hf : HasDerivAt
      (fun s : Real =>
        (fun z : PhaseSpace => radialDist z.2 ^ (2 : Nat) * X_u u z - inner ℝ z.1 z.2 * P_u u z)
          (z.1, z.2 + s • basisVec i))
      (2 * z.2 i * X_u u z - z.1 i * P_u u z - inner ℝ z.1 z.2 * u i) 0 := by
    simpa using hasDerivAt_pPath_F_u u i z
  have hg : HasDerivAt
      (fun s : Real => X_u u (z.1, z.2 + s • basisVec i) / radialDist z.1)
      0 0 := by
    simpa using hasDerivAt_pPath_U_scalar u i z
  convert (hf.sub (hg.const_mul (mp.m * gp.mu))) using 1
  · funext s
    simp [A_u_eq_observables, div_eq_mul_inv]
  · simpa using partialP_A_u mp gp u i z

lemma hasDerivAt_qPath_K_u_of_radialDist_ne_zero
    (mp : MassParam) (gp : GravitationalParam) (h : Real)
    (u : Vec3) (i : Fin 3) (z : PhaseSpace) (hr : radialDist z.1 ≠ 0) :
    HasDerivAt (fun s : Real => K_u mp gp h u (z.1 + s • basisVec i, z.2))
      (partialQ (K_u mp gp h u) i z) 0 := by
  simpa [K_u] using
    hasDerivAt_qPath_A_u_of_radialDist_ne_zero mp gp
      ((1 / Real.sqrt (-2 * mp.m * h)) • u) i z hr

lemma hasDerivAt_pPath_K_u
    (mp : MassParam) (gp : GravitationalParam) (h : Real)
    (u : Vec3) (i : Fin 3) (z : PhaseSpace) :
    HasDerivAt (fun s : Real => K_u mp gp h u (z.1, z.2 + s • basisVec i))
      (partialP (K_u mp gp h u) i z) 0 := by
  simpa [K_u] using
    hasDerivAt_pPath_A_u mp gp ((1 / Real.sqrt (-2 * mp.m * h)) • u) i z

lemma partialQ_mu_h_of_radialDist_ne_zero
    (mp : MassParam) (gp : GravitationalParam) (h : Real) (uv : Vec3 × Vec3)
    (i : Fin 3) (z : PhaseSpace) (hr : radialDist z.1 ≠ 0) :
    partialQ (mu_h mp gp h uv) i z =
      partialQ (L_u uv.1) i z + partialQ (K_u mp gp h uv.2) i z := by
  simpa [partialQ, mu_h] using
    (hasDerivAt_qPath_L_u uv.1 i z).add (hasDerivAt_qPath_K_u_of_radialDist_ne_zero mp gp h uv.2 i z hr) |>.deriv

lemma partialP_mu_h
    (mp : MassParam) (gp : GravitationalParam) (h : Real) (uv : Vec3 × Vec3)
    (i : Fin 3) (z : PhaseSpace) :
    partialP (mu_h mp gp h uv) i z =
      partialP (L_u uv.1) i z + partialP (K_u mp gp h uv.2) i z := by
  simpa [partialP, mu_h] using
    (hasDerivAt_pPath_L_u uv.1 i z).add (hasDerivAt_pPath_K_u mp gp h uv.2 i z) |>.deriv

lemma poisson_mu_h_expand
    (mp : MassParam) (gp : GravitationalParam) (h : Real)
    (uv uv' : Vec3 × Vec3) (z : PhaseSpace) (hr : radialDist z.1 ≠ 0) :
    poissonBracket (mu_h mp gp h uv) (mu_h mp gp h uv') z =
      poissonBracket (L_u uv.1) (L_u uv'.1) z +
        poissonBracket (L_u uv.1) (K_u mp gp h uv'.2) z +
        poissonBracket (K_u mp gp h uv.2) (L_u uv'.1) z +
        poissonBracket (K_u mp gp h uv.2) (K_u mp gp h uv'.2) z := by
  unfold poissonBracket
  rw [partialQ_mu_h_of_radialDist_ne_zero mp gp h uv 0 z hr,
    partialQ_mu_h_of_radialDist_ne_zero mp gp h uv 1 z hr,
    partialQ_mu_h_of_radialDist_ne_zero mp gp h uv 2 z hr,
    partialQ_mu_h_of_radialDist_ne_zero mp gp h uv' 0 z hr,
    partialQ_mu_h_of_radialDist_ne_zero mp gp h uv' 1 z hr,
    partialQ_mu_h_of_radialDist_ne_zero mp gp h uv' 2 z hr,
    partialP_mu_h mp gp h uv 0 z,
    partialP_mu_h mp gp h uv 1 z,
    partialP_mu_h mp gp h uv 2 z,
    partialP_mu_h mp gp h uv' 0 z,
    partialP_mu_h mp gp h uv' 1 z,
    partialP_mu_h mp gp h uv' 2 z]
  ring

theorem poisson_K_u_L_u
    (mp : MassParam) (gp : GravitationalParam) (h : Real)
    (u v : Vec3) (z : PhaseSpace) (hr : radialDist z.1 ≠ 0) :
    poissonBracket (K_u mp gp h u) (L_u v) z =
      K_u mp gp h (cross u v) z := by
  have hcross : cross v u = -cross u v := by
    ext i
    fin_cases i <;> simp [cross, cross_apply]
    · ring
    · ring
    · ring
  calc
    poissonBracket (K_u mp gp h u) (L_u v) z
        = -poissonBracket (L_u v) (K_u mp gp h u) z := by
            rw [poissonBracket_skew]
    _ = -(K_u mp gp h (cross v u) z) := by
          rw [poisson_L_u_K_u mp gp h v u z hr]
    _ = K_u mp gp h (cross u v) z := by
          rw [hcross]
          simp [K_u, A_u]
          ring

theorem hidden_so4_component_algebra
    (mp : MassParam) (gp : GravitationalParam) (h : Real)
    (u v u' v' : Vec3) (z : PhaseSpace)
    (hz : keplerHamiltonian mp gp z = h) (hh : h < 0) (hr : radialDist z.1 ≠ 0) :
    poissonBracket (L_u u) (L_u u') z = L_u (cross u u') z ∧
    poissonBracket (L_u u) (K_u mp gp h v') z = K_u mp gp h (cross u v') z ∧
    poissonBracket (K_u mp gp h v) (L_u u') z = K_u mp gp h (cross v u') z ∧
    poissonBracket (K_u mp gp h v) (K_u mp gp h v') z = L_u (cross v v') z := by
  constructor
  · exact poisson_L_u_L_v u u' z
  · constructor
    · exact poisson_L_u_K_u mp gp h u v' z hr
    · constructor
      · exact poisson_K_u_L_u mp gp h v u' z hr
      · exact poisson_K_u_K_u mp gp h v v' z hz hh hr

theorem rotational_comoment
    (mp : MassParam) (gp : GravitationalParam)
    (u v w : Vec3) (z : PhaseSpace) :
    poissonBracket (X_u v) (L_u u) z = X_u (cross v u) z ∧
    poissonBracket (P_u v) (L_u u) z = P_u (cross v u) z ∧
    poissonBracket (L_u u) (L_u w) z = L_u (cross u w) z ∧
    poissonBracket (L_u u) (keplerHamiltonian mp gp) z = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using congrFun (poisson_X_v_L_u_and_P_v_L_u u v).1 z
  · simpa using congrFun (poisson_X_v_L_u_and_P_v_L_u u v).2 z
  · exact poisson_L_u_L_v u w z
  · exact poisson_L_u_H mp gp u z

theorem LA_poisson_algebra
    (mp : MassParam) (gp : GravitationalParam)
    (u v : Vec3) (z : PhaseSpace) (hr : radialDist z.1 ≠ 0) :
    poissonBracket (L_u u) (L_u v) z = L_u (cross u v) z ∧
    poissonBracket (L_u u) (A_u mp gp v) z = A_u mp gp (cross u v) z ∧
    poissonBracket (A_u mp gp u) (A_u mp gp v) z =
      -2 * mp.m * keplerHamiltonian mp gp z * L_u (cross u v) z ∧
    poissonBracket (L_u u) (keplerHamiltonian mp gp) z = 0 ∧
    poissonBracket (A_u mp gp u) (keplerHamiltonian mp gp) z = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact poisson_L_u_L_v u v z
  · exact poisson_L_u_A_u mp gp u v z hr
  · exact poisson_A_u_A_u mp gp u v z hr
  · exact poisson_L_u_H mp gp u z
  · exact poisson_A_u_H mp gp u z hr

theorem hidden_so4_shell_algebra
    (mp : MassParam) (gp : GravitationalParam) (h : Real)
    (u v u' v' : Vec3) (z : NegativeEnergyShell mp gp h) (hh : h < 0) :
    poissonBracket (L_u u) (L_u u') z.1 = L_u (cross u u') z.1 ∧
    poissonBracket (L_u u) (K_u mp gp h v') z.1 = K_u mp gp h (cross u v') z.1 ∧
    poissonBracket (K_u mp gp h v) (L_u u') z.1 = K_u mp gp h (cross v u') z.1 ∧
    poissonBracket (K_u mp gp h v) (K_u mp gp h v') z.1 = L_u (cross v v') z.1 := by
  exact hidden_so4_component_algebra mp gp h u v u' v' z.1 z.2.1 hh z.2.2

theorem hidden_so4_comoment
    (mp : MassParam) (gp : GravitationalParam) (h : Real)
    (uv uv' : Vec3 × Vec3) (z : NegativeEnergyShell mp gp h) (hh : h < 0) :
    poissonBracket (mu_h mp gp h uv) (mu_h mp gp h uv') z.1 =
      mu_h mp gp h (so4ModelBracket uv uv') z.1 := by
  have hexpand := poisson_mu_h_expand mp gp h uv uv' z.1 z.2.2
  have hcomp :=
    hidden_so4_shell_algebra mp gp h uv.1 uv.2 uv'.1 uv'.2 z hh
  rcases hcomp with ⟨hLL, hLK, hKL, hKK⟩
  have hLadd :=
    congrFun (L_u_add (cross uv.1 uv'.1) (cross uv.2 uv'.2)) z.1
  have hKadd :=
    congrFun (K_u_add mp gp h (cross uv.1 uv'.2) (cross uv.2 uv'.1)) z.1
  calc
    poissonBracket (mu_h mp gp h uv) (mu_h mp gp h uv') z.1
        =
          poissonBracket (L_u uv.1) (L_u uv'.1) z.1 +
            poissonBracket (L_u uv.1) (K_u mp gp h uv'.2) z.1 +
            poissonBracket (K_u mp gp h uv.2) (L_u uv'.1) z.1 +
            poissonBracket (K_u mp gp h uv.2) (K_u mp gp h uv'.2) z.1 := hexpand
    _ =
          L_u (cross uv.1 uv'.1) z.1 +
            K_u mp gp h (cross uv.1 uv'.2) z.1 +
            K_u mp gp h (cross uv.2 uv'.1) z.1 +
            L_u (cross uv.2 uv'.2) z.1 := by rw [hLL, hLK, hKL, hKK]
    _ =
          L_u (cross uv.1 uv'.1 + cross uv.2 uv'.2) z.1 +
            K_u mp gp h (cross uv.1 uv'.2 + cross uv.2 uv'.1) z.1 := by
          rw [hLadd, hKadd]
          ring
    _ = mu_h mp gp h (so4ModelBracket uv uv') z.1 := by
          simp [mu_h, so4ModelBracket]

theorem hidden_so4_comoment_source
    (mp : MassParam) (gp : GravitationalParam) (h : Real)
    (uv uv' : Vec3 × Vec3) (z : NegativeEnergyShell mp gp h) (hh : h < 0) :
    Function.Bijective Phi ∧
    poissonBracket (mu_h mp gp h uv) (mu_h mp gp h uv') z.1 =
      mu_h mp gp h (so4ModelBracket uv uv') z.1 := by
  exact ⟨so4_model_isomorphic_to_so4.1, hidden_so4_comoment mp gp h uv uv' z hh⟩

theorem so4ModelBracket_Jplus_pair
    (u v : Vec3) :
    so4ModelBracket (((1 / 2 : Real) • u), ((1 / 2 : Real) • u))
        (((1 / 2 : Real) • v), ((1 / 2 : Real) • v)) =
      (((1 / 2 : Real) • cross u v), ((1 / 2 : Real) • cross u v)) := by
  apply Prod.ext
  · ext j <;> fin_cases j <;> simp [so4ModelBracket, cross, cross_apply] <;> ring
  · ext j <;> fin_cases j <;> simp [so4ModelBracket, cross, cross_apply] <;> ring

theorem so4ModelBracket_Jminus_pair
    (u v : Vec3) :
    so4ModelBracket (((1 / 2 : Real) • u), (-(1 / 2 : Real) • u))
        (((1 / 2 : Real) • v), (-(1 / 2 : Real) • v)) =
      (((1 / 2 : Real) • cross u v), (-(1 / 2 : Real) • cross u v)) := by
  apply Prod.ext
  · ext j <;> fin_cases j <;> simp [so4ModelBracket, cross, cross_apply] <;> ring
  · ext j <;> fin_cases j <;> simp [so4ModelBracket, cross, cross_apply] <;> ring

theorem so4ModelBracket_Jplus_Jminus_pair
    (u v : Vec3) :
    so4ModelBracket (((1 / 2 : Real) • u), ((1 / 2 : Real) • u))
        (((1 / 2 : Real) • v), (-(1 / 2 : Real) • v)) =
      (0, 0) := by
  apply Prod.ext
  · ext j <;> fin_cases j <;> simp [so4ModelBracket, cross, cross_apply] <;> ring
  · ext j <;> fin_cases j <;> simp [so4ModelBracket, cross, cross_apply] <;> ring

def JplusModel (u : Vec3) : Vec3 × Vec3 :=
  (((1 / 2 : Real) • u), ((1 / 2 : Real) • u))

def JminusModel (u : Vec3) : Vec3 × Vec3 :=
  (((1 / 2 : Real) • u), (-(1 / 2 : Real) • u))

def Jplus_u (mp : MassParam) (gp : GravitationalParam) (h : Real) (u : Vec3) :
    PhaseSpace -> Real :=
  mu_h mp gp h (JplusModel u)

def Jminus_u (mp : MassParam) (gp : GravitationalParam) (h : Real) (u : Vec3) :
    PhaseSpace -> Real :=
  mu_h mp gp h (JminusModel u)

theorem so4ModelBracket_JplusModel
    (u v : Vec3) :
    so4ModelBracket (JplusModel u) (JplusModel v) =
      JplusModel (cross u v) := by
  simpa [JplusModel] using so4ModelBracket_Jplus_pair u v

theorem so4ModelBracket_JminusModel
    (u v : Vec3) :
    so4ModelBracket (JminusModel u) (JminusModel v) =
      JminusModel (cross u v) := by
  simpa [JminusModel] using so4ModelBracket_Jminus_pair u v

theorem so4ModelBracket_JplusModel_JminusModel
    (u v : Vec3) :
    so4ModelBracket (JplusModel u) (JminusModel v) = (0, 0) := by
  simpa [JplusModel, JminusModel] using so4ModelBracket_Jplus_Jminus_pair u v

theorem poisson_Jplus_u_Jplus_u
    (mp : MassParam) (gp : GravitationalParam) (h : Real)
    (u v : Vec3) (z : NegativeEnergyShell mp gp h) (hh : h < 0) :
    poissonBracket (Jplus_u mp gp h u) (Jplus_u mp gp h v) z.1 =
      Jplus_u mp gp h (cross u v) z.1 := by
  have hmu := hidden_so4_comoment mp gp h (JplusModel u) (JplusModel v) z hh
  rw [so4ModelBracket_JplusModel] at hmu
  simpa [Jplus_u] using hmu

theorem poisson_Jminus_u_Jminus_u
    (mp : MassParam) (gp : GravitationalParam) (h : Real)
    (u v : Vec3) (z : NegativeEnergyShell mp gp h) (hh : h < 0) :
    poissonBracket (Jminus_u mp gp h u) (Jminus_u mp gp h v) z.1 =
      Jminus_u mp gp h (cross u v) z.1 := by
  have hmu := hidden_so4_comoment mp gp h (JminusModel u) (JminusModel v) z hh
  rw [so4ModelBracket_JminusModel] at hmu
  simpa [Jminus_u] using hmu

theorem poisson_Jplus_u_Jminus_u
    (mp : MassParam) (gp : GravitationalParam) (h : Real)
    (u v : Vec3) (z : NegativeEnergyShell mp gp h) (hh : h < 0) :
    poissonBracket (Jplus_u mp gp h u) (Jminus_u mp gp h v) z.1 = 0 := by
  have hmu := hidden_so4_comoment mp gp h (JplusModel u) (JminusModel v) z hh
  rw [so4ModelBracket_JplusModel_JminusModel, mu_h_zero] at hmu
  simpa [Jplus_u, Jminus_u] using hmu

theorem two_commuting_so3
    (mp : MassParam) (gp : GravitationalParam) (h : Real)
    (u v : Vec3) (z : NegativeEnergyShell mp gp h) (hh : h < 0) :
    poissonBracket (Jplus_u mp gp h u) (Jplus_u mp gp h v) z.1 =
      Jplus_u mp gp h (cross u v) z.1 ∧
    poissonBracket (Jminus_u mp gp h u) (Jminus_u mp gp h v) z.1 =
      Jminus_u mp gp h (cross u v) z.1 ∧
    poissonBracket (Jplus_u mp gp h u) (Jminus_u mp gp h v) z.1 = 0 := by
  exact ⟨poisson_Jplus_u_Jplus_u mp gp h u v z hh,
    poisson_Jminus_u_Jminus_u mp gp h u v z hh,
    poisson_Jplus_u_Jminus_u mp gp h u v z hh⟩

end

end Kepler
