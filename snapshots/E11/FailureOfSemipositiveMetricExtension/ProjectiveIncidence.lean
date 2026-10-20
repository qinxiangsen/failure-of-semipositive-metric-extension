import FailureOfSemipositiveMetricExtension.ProjectiveLine
import FailureOfSemipositiveMetricExtension.BlowupProper

/-!
The incidence relation between a complex affine vector and a projective line is
closed. The previously constructed affine blow-up atlas is proved equal to the
induced incidence-subspace topology. The proof uses the already established
proper blow-down, continuous direction map, and a proper injective inclusion;
there is no assumption of continuity of a chosen homogeneous representative.
-/

noncomputable section

namespace FailureOfSemipositiveMetricExtension.ProjectiveIncidence

open Set Topology

abbrev Ambient := Blowup.Plane × ProjectiveLine.Point

/-- The universal affine/projective incidence relation. -/
def incidence : Set Ambient := {p | p.1 ∈ p.2.submodule}

/-- In the first projective chart, incidence is one polynomial equation. -/
theorem mem_lineX_iff (w : Blowup.Plane) (s : ℂ) :
    w ∈ (Blowup.lineX s).submodule ↔ w 1 = w 0*s := by
  rw [Blowup.lineX, Projectivization.submodule_mk, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a,ha⟩
    rw [← ha]
    simp [Blowup.vectorX]
  · intro h
    refine ⟨w 0,?_⟩
    ext i; fin_cases i <;> simp [Blowup.vectorX,h]

/-- In the second projective chart, incidence is the complementary polynomial equation. -/
theorem mem_lineY_iff (w : Blowup.Plane) (s : ℂ) :
    w ∈ (Blowup.lineY s).submodule ↔ w 0 = w 1*s := by
  rw [Blowup.lineY, Projectivization.submodule_mk, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a,ha⟩
    rw [← ha]
    simp [Blowup.vectorY]
  · intro h
    refine ⟨w 1,?_⟩
    ext i; fin_cases i <;> simp [Blowup.vectorY,h]

/-- The projective direction map is continuous for the already constructed blow-up atlas. -/
theorem direction_continuous : Continuous Blowup.direction := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  rcases Blowup.charts_cover p with ⟨r,s,rfl⟩ | ⟨r,s,rfl⟩
  · apply (Blowup.homeomorphChartX.symm.continuousAt_iff_continuousAt_comp_right
      (show Blowup.X r s ∈ Blowup.homeomorphChartX.source from ⟨s,rfl⟩)).mpr
    have hc : Continuous (Blowup.direction ∘ Blowup.homeomorphChartX.symm) :=
      (ProjectiveLine.param_continuous 0).comp continuous_snd
    exact hc.continuousAt
  · apply (Blowup.homeomorphChartY.symm.continuousAt_iff_continuousAt_comp_right
      (show Blowup.Y r s ∈ Blowup.homeomorphChartY.source from ⟨s,rfl⟩)).mpr
    have hc : Continuous (Blowup.direction ∘ Blowup.homeomorphChartY.symm) :=
      (ProjectiveLine.param_continuous 1).comp continuous_snd
    exact hc.continuousAt

/-- Inclusion of the actual incidence-point type into its affine/projective ambient space. -/
def inclusion (p : Blowup.Point) : Ambient := (Blowup.projection p,Blowup.direction p)

theorem inclusion_injective : Function.Injective inclusion := by
  intro p q h
  exact Subtype.ext h

theorem inclusion_continuous : Continuous inclusion :=
  Blowup.projection_continuous.prodMk direction_continuous

/-- Properness is inherited from the known proper blow-down by the Hausdorff intermediate space. -/
theorem inclusion_isProperMap : IsProperMap inclusion :=
  isProperMap_of_comp_of_t2 (f := inclusion) (g := Prod.fst)
    inclusion_continuous continuous_fst Blowup.projection_isProperMap

/-- The constructed blow-up is a closed embedded subspace of `ℂ² × ℙ¹`. -/
theorem inclusion_isClosedEmbedding : IsClosedEmbedding inclusion :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap inclusion_continuous
    inclusion_injective inclusion_isProperMap.isClosedMap

/-- Precisely the universal incidence relation is the image of this closed embedding. -/
theorem range_inclusion : range inclusion = incidence := by
  ext p
  constructor
  · rintro ⟨q,rfl⟩
    exact q.property
  · intro hp
    exact ⟨⟨p,hp⟩,rfl⟩

/-- Closedness of the actual vector/projective-line incidence relation. -/
theorem incidence_isClosed : IsClosed incidence := by
  rw [← range_inclusion]
  exact inclusion_isClosedEmbedding.isClosed_range

/-- A direct form usable for pulling incidence back along continuous families. -/
theorem isClosed_incidence :
    IsClosed {p : Blowup.Plane × ProjectiveLine.Point | p.1 ∈ p.2.submodule} :=
  incidence_isClosed

/-- The affine blow-up atlas topology really is the ambient incidence-subspace topology. -/
theorem blowup_topology_eq_induced :
    Blowup.instTopologicalSpacePoint =
      TopologicalSpace.induced inclusion (inferInstance : TopologicalSpace Ambient) :=
  inclusion_isClosedEmbedding.isEmbedding.isInducing.eq_induced

/-- Continuous vector and projective-direction families have a closed incidence locus. -/
theorem incidence_preimage_isClosed {T : Type*} [TopologicalSpace T]
    (v : T → Blowup.Plane) (d : T → ProjectiveLine.Point)
    (hv : Continuous v) (hd : Continuous d) :
    IsClosed {t | v t ∈ (d t).submodule} :=
  isClosed_incidence.preimage (hv.prodMk hd)

/-- Nonzero scalar changes of affine representative preserve incidence. -/
theorem smul_mem_iff (a : ℂ) (ha : a ≠ 0) (w : Blowup.Plane) (d : ProjectiveLine.Point) :
    a • w ∈ d.submodule ↔ w ∈ d.submodule := d.submodule.smul_mem_iff ha

end FailureOfSemipositiveMetricExtension.ProjectiveIncidence
