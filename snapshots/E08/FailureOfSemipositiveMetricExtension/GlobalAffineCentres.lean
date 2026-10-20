import FailureOfSemipositiveMetricExtension.GlobalIncidence

/-!
Affine normalizations centred at the four sections of the global incidence model.
Their zero coordinates are the specified centres, their centre-ideal pairs are
exactly the affine coordinates, and they cover projective space after removing
all the other centres from each chart.
-/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section

/-- The standard homogeneous coordinate used to normalize each centred chart. -/
def baseChart : Fin 4 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 2

/-- Homogeneous coordinates in the affine chart centred at the selected section. -/
def baseVector : Fin 4 → ℂ → Blowup.Plane → (Fin 3 → ℂ)
  | 0, _, w => ![1,w 0,w 1]
  | 1, _, w => ![w 0,1,w 1]
  | 2, t, w => ![1,1+w 0,t+w 1]
  | 3, _, w => ![w 0,w 1,1]

@[simp] theorem baseVector_normalized (i : Fin 4) (t : ℂ) (w : Blowup.Plane) :
    baseVector i t w (baseChart i) = 1 := by
  fin_cases i <;> simp [baseVector,baseChart]

theorem baseVector_ne_zero (i : Fin 4) (t : ℂ) (w : Blowup.Plane) :
    baseVector i t w ≠ 0 := by
  intro h
  have hi := congrFun h (baseChart i)
  simpa using hi

/-- The actual projective base point parametrized by centred affine coordinates. -/
def affineBase (i : Fin 4) (t : ℂ) (w : Blowup.Plane) : PlanePoint :=
  Projectivization.mk ℂ (baseVector i t w) (baseVector_ne_zero i t w)

@[simp] theorem pairMap_baseVector (i : Fin 4) (t : ℂ) (w : Blowup.Plane) :
    pairMap i t (baseVector i t w) = w := by
  ext k
  fin_cases i <;> fin_cases k <;> simp [pairMap,pair,baseVector]

theorem affineBase_injective (i : Fin 4) (t : ℂ) : Function.Injective (affineBase i t) := by
  intro w w' h
  rcases (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h with ⟨a,ha⟩
  have ha1 : a = 1 := by
    simpa using congrFun ha (baseChart i)
  have hv : baseVector i t w = baseVector i t w' := by
    simpa [ha1] using ha.symm
  simpa using congrArg (pairMap i t) hv

@[simp] theorem baseVector_zero (i : Fin 4) (t : ℂ) :
    baseVector i t 0 = centreVector i t := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [baseVector,centreVector,Coordinates.p₁,Coordinates.p₂,Coordinates.p₃,Coordinates.p₄]

@[simp] theorem affineBase_zero (i : Fin 4) (t : ℂ) :
    affineBase i t 0 = centre i t := by
  unfold affineBase
  simp only [baseVector_zero,centre_mk]

/-- The selected global incidence equation is the ordinary affine blow-up incidence. -/
theorem incidence_affineBase_iff (i : Fin 4) (t : ℂ) (w : Blowup.Plane) (d : Direction) :
    Incidence (affineBase i t w) d i t ↔ w ∈ d.submodule := by
  rw [affineBase,incidence_mk_iff,pairMap_baseVector]

/-- Translation from centred coordinates to the ordinary projective affine chart. -/
def baseCoordinates : Fin 4 → ℂ → Blowup.Plane → (ℂ × ℂ)
  | 0, _, w => (w 0,w 1)
  | 1, _, w => (w 0,w 1)
  | 2, t, w => (1+w 0,t+w 1)
  | 3, _, w => (w 0,w 1)

theorem affineBase_eq_param (i : Fin 4) (t : ℂ) (w : Blowup.Plane) :
    affineBase i t w = ProjectivePlane.param (baseChart i) (baseCoordinates i t w) := by
  fin_cases i <;> rfl

theorem affineBase_mem_chartSet (i : Fin 4) (t : ℂ) (w : Blowup.Plane) :
    affineBase i t w ∈ ProjectivePlane.chartSet (baseChart i) := by
  rw [affineBase_eq_param]
  exact ProjectivePlane.param_mem_chartSet _ _

/-- The translated centred chart has exactly the ordinary affine-chart range. -/
theorem affineBase_range (i : Fin 4) (t : ℂ) :
    Set.range (affineBase i t) = ProjectivePlane.chartSet (baseChart i) := by
  ext p
  constructor
  · rintro ⟨w,rfl⟩
    exact affineBase_mem_chartSet i t w
  · rintro ⟨q,rfl⟩
    fin_cases i
    · exact ⟨![q.1,q.2],rfl⟩
    · exact ⟨![q.1,q.2],rfl⟩
    · refine ⟨![q.1-1,q.2-t],?_⟩
      rw [affineBase_eq_param]
      congr 1
      ext <;> simp [baseCoordinates]
    · exact ⟨![q.1,q.2],rfl⟩

/-- Every base point admits centred coordinates avoiding the other three centres. -/
theorem affineBase_cover_avoiding (p : PlanePoint) (t : ℂ) :
    ∃ i w, p = affineBase i t w ∧ ∀ j, j ≠ i → p ≠ centre j t := by
  classical
  by_cases hc : ∃ i, p = centre i t
  · obtain ⟨i,hi⟩ := hc
    refine ⟨i,0,hi.trans (affineBase_zero i t).symm,?_⟩
    intro j hj hp
    exact hj ((centre_injective t) (hp.symm.trans hi))
  · have haway : ∀ j, p ≠ centre j t := by
      intro j hj
      exact hc ⟨j,hj⟩
    obtain ⟨k,q,hq⟩ := ProjectivePlane.charts_cover p
    fin_cases k
    · exact ⟨0,![q.1,q.2],hq,fun j _ => haway j⟩
    · exact ⟨1,![q.1,q.2],hq,fun j _ => haway j⟩
    · exact ⟨3,![q.1,q.2],hq,fun j _ => haway j⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
