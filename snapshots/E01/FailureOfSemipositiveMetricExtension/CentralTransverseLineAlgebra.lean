import FailureOfSemipositiveMetricExtension.GenericConicAnalytic

/-! Lines through the fourth central centre, avoiding the other three centres.
Their four actual incidence directions have homogeneous degrees 1,1,1,0. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine
noncomputable section
open Set

structure Data where
  slope : ℂ
  slope_ne_zero : slope ≠ 0
  sub_ne_zero : slope - 1 ≠ 0

def baseVector (c : Data) (v : Blowup.Plane) : Fin 3 → ℂ := ![v 0,c.slope*v 0,v 1]

def baseMap (c : Data) : Blowup.Plane →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun := baseVector c
  map_add' v w := by ext j; fin_cases j <;> simp [baseVector] <;> ring
  map_smul' a v := by ext j; fin_cases j <;> simp [baseVector] <;> ring

theorem baseMap_injective (c : Data) : Function.Injective (baseMap c) := by
  intro v w h
  have h0 := congrFun h 0
  have h1 := congrFun h 2
  ext j; fin_cases j
  · exact h0
  · exact h1

theorem baseVector_smul (c : Data) (a : ℂ) (v : Blowup.Plane) :
    baseVector c (a • v) = a • baseVector c v := (baseMap c).map_smul a v

theorem baseVector_ne_zero (c : Data) (v : Blowup.Plane) (hv : v ≠ 0) :
    baseVector c v ≠ 0 := by
  intro h
  apply hv
  apply baseMap_injective c
  exact h.trans (map_zero (baseMap c)).symm

def scale (c : Data) (r : Fin 4) : ℂ := match r with
  | 0 => c.slope
  | 1 => 1
  | 2 => c.slope-1
  | 3 => 1

theorem scale_ne_zero (c : Data) (r : Fin 4) : scale c r ≠ 0 := by
  fin_cases r
  · exact c.slope_ne_zero
  · exact one_ne_zero
  · exact c.sub_ne_zero
  · exact one_ne_zero

def scaledMap (c : Data) (r : Fin 4) : Blowup.Plane →ₗ[ℂ] Blowup.Plane where
  toFun v := ![scale c r*v 0,v 1]
  map_add' v w := by ext j; fin_cases j <;> simp <;> ring
  map_smul' a v := by ext j; fin_cases j <;> simp <;> ring

theorem scaledMap_injective (c : Data) (r : Fin 4) : Function.Injective (scaledMap c r) := by
  intro v w h
  have h0 : v 0 = w 0 := mul_left_cancel₀ (scale_ne_zero c r) (congrFun h 0)
  have h1 := congrFun h 1
  ext j; fin_cases j
  · exact h0
  · exact h1

def directionVector (c : Data) (r : Fin 4) (v : Blowup.Plane) : Blowup.Plane :=
  if r = 3 then Blowup.vectorX c.slope else scaledMap c r v

theorem directionVector_ne_zero (c : Data) (r : Fin 4) (v : Blowup.Plane) (hv : v ≠ 0) :
    directionVector c r v ≠ 0 := by
  by_cases hr : r = 3
  · simpa [directionVector,hr] using Blowup.vectorX_ne_zero c.slope
  · simp only [directionVector,if_neg hr]
    intro h
    exact hv (scaledMap_injective c r (h.trans (map_zero (scaledMap c r)).symm))

def incidenceFactor (r : Fin 4) (v : Blowup.Plane) : ℂ := if r = 3 then v 0 else 1

theorem pairMap_baseVector (c : Data) (r : Fin 4) (v : Blowup.Plane) :
    pairMap r 0 (baseVector c v) = incidenceFactor r v • directionVector c r v := by
  fin_cases r <;> ext j <;> fin_cases j <;>
    simp [pairMap,pair,baseVector,incidenceFactor,directionVector,scaledMap,scale,Blowup.vectorX] <;> ring

def base (c : Data) : Direction → PlanePoint := Projectivization.map (baseMap c) (baseMap_injective c)

theorem base_mk (c : Data) (v : Blowup.Plane) (hv : v ≠ 0) :
    base c (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (baseVector c v) (baseVector_ne_zero c v hv) := rfl

def direction (c : Data) (r : Fin 4) (d : Direction) : Direction :=
  if r = 3 then Blowup.lineX c.slope else
    Projectivization.map (scaledMap c r) (scaledMap_injective c r) d

theorem direction_mk (c : Data) (r : Fin 4) (v : Blowup.Plane) (hv : v ≠ 0) :
    direction c r (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (directionVector c r v) (directionVector_ne_zero c r v hv) := by
  by_cases hr : r = 3 <;> simp only [direction,directionVector,hr,if_true,if_false]
  · rfl
  · rfl

@[simp] theorem direction_one (c : Data) (d : Direction) : direction c 1 d = d := by
  induction d using Projectivization.ind with
  | h v hv =>
    rw [direction_mk]
    congr 1
    ext j; fin_cases j <;> simp [directionVector,scaledMap,scale]

@[simp] theorem direction_three (c : Data) (d : Direction) :
    direction c 3 d = Blowup.lineX c.slope := by simp [direction]

theorem incidence (c : Data) (d : Direction) (r : Fin 4) :
    Incidence (base c d) (direction c r d) r 0 := by
  induction d using Projectivization.ind with
  | h v hv =>
    rw [base_mk,direction_mk,incidence_mk_iff,Projectivization.submodule_mk,Submodule.mem_span_singleton]
    exact ⟨incidenceFactor r v,(pairMap_baseVector c r v).symm⟩

def param (c : Data) (d : Direction) : Fiber 0 :=
  ⟨(base c d,fun r => direction c r d),incidence c d⟩

@[simp] theorem param_blowdown (c : Data) (d : Direction) : FixedFiber.blowdown 0 (param c d) = base c d := rfl
@[simp] theorem param_direction (c : Data) (r : Fin 4) (d : Direction) :
    FixedFiber.direction 0 r (param c d) = direction c r d := rfl
@[simp] theorem param_direction_one (c : Data) (d : Direction) :
    FixedFiber.direction 0 1 (param c d) = d := direction_one c d

theorem param_injective (c : Data) : Function.Injective (param c) := by
  intro d e h
  simpa only [param_direction_one] using congrArg (FixedFiber.direction 0 1) h

/-- Every parametrized line avoids the first three central blow-up centres. -/
theorem base_away_first_three (c : Data) (d : Direction) (r : Fin 4) (hr : r ≠ 3) :
    base c d ≠ centre r 0 := by
  induction d using Projectivization.ind with
  | h v hv =>
    rw [base_mk]
    intro h
    have hm := (projective_eq_iff_mem (baseVector c v) (baseVector_ne_zero c v hv) (centre r 0)).mp h
    have hz := (pairMap_zero_iff_mem_centre r 0 (baseVector c v)).mpr hm
    rw [pairMap_baseVector,incidenceFactor,if_neg hr,one_smul] at hz
    exact directionVector_ne_zero c r v hv hz

/-- The parameter [0:1] maps to the fourth exceptional curve. -/
theorem base_at_fourth (c : Data) : base c (ProjectiveLine.param 1 0) = centre 3 0 := by
  rw [ProjectiveLine.param_eq_mk_sourceVector,base_mk,← centre_mk]
  congr 1
  ext j
  fin_cases j <;> simp [baseVector,ProjectiveLine.sourceVector,Blowup.vectorY,centreVector,Coordinates.p₄]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine
