import FailureOfSemipositiveMetricExtension.HisamotoLocalTopology

/-! Four actual affine charts give the one-point incidence surface its analytic
manifold structure, preserving the inherited projective-product topology. The
ruling product maps are analytic in both directions. -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

abbrev Coord := ℂ × ℂ

def affineChart (i j : Fin 2) : PartialHomeomorph Point Coord :=
  (rulingProductChart i).trans ((ProjectiveLine.homeomorphChart j).prod (PartialHomeomorph.refl ℂ))

def affineParam (i j : Fin 2) (q : Coord) : Point :=
  localParam i (ProjectiveLine.param j q.1,q.2)

@[simp] theorem affineChart_apply (i j : Fin 2) (q : Point) :
    affineChart i j q = (ProjectiveLine.coordinates j (fiberDirection i (blowdown q)),
      ProjectiveLine.coordinates i (ruling q)) := rfl
@[simp] theorem affineChart_symm_apply (i j : Fin 2) (q : Coord) :
    (affineChart i j).symm q = affineParam i j q := rfl
@[simp] theorem affineChart_target (i j : Fin 2) : (affineChart i j).target = univ := by
  simp [affineChart,PartialHomeomorph.trans_target,rulingProductChart]

@[simp] theorem mem_affineChart_source (i j : Fin 2) (q : Point) :
    q ∈ (affineChart i j).source ↔ q ∈ rulingChart i ∧
      fiberDirection i (blowdown q) ∈ ProjectiveLine.chartSet j := by
  simp [affineChart,PartialHomeomorph.trans_source,rulingProductChart,localCoordinates]

theorem affineCharts_cover (q : Point) : ∃ ij : Fin 2 × Fin 2, q ∈ (affineChart ij.1 ij.2).source := by
  obtain ⟨i,hi⟩ := ruling_charts_cover q
  obtain ⟨j,s,hs⟩ := ProjectiveLine.charts_cover (fiberDirection i (blowdown q))
  exact ⟨(i,j),(mem_affineChart_source i j q).mpr ⟨hi,s,hs.symm⟩⟩

instance instChartedSpacePoint : ChartedSpace Coord Point where
  atlas := range (fun ij : Fin 2 × Fin 2 => affineChart ij.1 ij.2)
  chartAt q := affineChart (Classical.choose (affineCharts_cover q)).1
    (Classical.choose (affineCharts_cover q)).2
  mem_chart_source q := Classical.choose_spec (affineCharts_cover q)
  chart_mem_atlas _ := ⟨_,rfl⟩

theorem affineChart_mem_atlas (i j : Fin 2) : affineChart i j ∈ atlas Coord Point := ⟨(i,j),rfl⟩

theorem affineParam_blowdown_contMDiff (i j : Fin 2) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) n (fun q => blowdown (affineParam i j q)) :=
  fiberPlane_param_contMDiff i j n

theorem affineParam_ruling_contMDiff (i j : Fin 2) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,Coord) 𝓘(ℂ) n (fun q => ruling (affineParam i j q)) :=
  (ProjectiveLine.param_contMDiff i n).comp contDiff_snd.contMDiff

/-- All sixteen affine changes are analytic on their actual open overlaps. -/
theorem affineChart_transition_contDiffOn (i j k l : Fin 2) (n : WithTop ℕ∞) :
    ContDiffOn ℂ n ((affineChart i j).symm.trans (affineChart k l))
      ((affineChart i j).symm.trans (affineChart k l)).source := by
  intro q hq
  have hs : affineParam i j q ∈ (affineChart k l).source := hq.2
  have hm := (mem_affineChart_source k l _).mp hs
  have hf := (fiberDirection_contMDiffAt k n (blowdown (affineParam i j q))
    (fiberProjection_rep_nonzero k _ hm.1)).comp q
      (affineParam_blowdown_contMDiff i j n).contMDiffAt
  have hx := ((ProjectiveLineBundle.coordinates_contMDiffOn l n).contMDiffAt
    ((ProjectiveLine.chartSet_isOpen l).mem_nhds hm.2)).comp q hf
  have ht := ((ProjectiveLineBundle.coordinates_contMDiffOn k n).contMDiffAt
    ((ProjectiveLine.chartSet_isOpen k).mem_nhds hm.1)).comp q
      (affineParam_ruling_contMDiff i j n).contMDiffAt
  exact (hx.prodMk_space ht).contDiffAt.contDiffWithinAt

instance instIsManifoldPoint (n : WithTop ℕ∞) : IsManifold 𝓘(ℂ,Coord) n Point := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨⟨i,j⟩,rfl⟩ ⟨⟨k,l⟩,rfl⟩
  simpa using affineChart_transition_contDiffOn i j k l n

theorem affineParam_contMDiff (i j : Fin 2) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) n (affineParam i j) := by
  have h := contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ,Coord)) (n := n) (affineChart_mem_atlas i j))
  rw [affineChart_target] at h
  exact contMDiffOn_univ.mp h

theorem affineCoordinates_contMDiffOn (i j : Fin 2) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) n (affineChart i j) (affineChart i j).source :=
  contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (affineChart_mem_atlas i j))

theorem contMDiff_of_affineParam {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ E H) (n : WithTop ℕ∞) {f : Point → N}
    (h : ∀ i j, ContMDiff 𝓘(ℂ,Coord) I n (fun q => f (affineParam i j q))) :
    ContMDiff 𝓘(ℂ,Coord) I n f := by
  intro p
  obtain ⟨⟨i,j⟩,hp⟩ := affineCharts_cover p
  have hc := (affineCoordinates_contMDiffOn i j n).contMDiffAt ((affineChart i j).open_source.mem_nhds hp)
  apply ((h i j).contMDiffAt.comp p hc).congr_of_eventuallyEq
  filter_upwards [(affineChart i j).open_source.mem_nhds hp] with q hq
  exact congrArg f ((affineChart i j).left_inv hq).symm

theorem blowdown_contMDiff (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) n blowdown :=
  contMDiff_of_affineParam _ n (fun i j => affineParam_blowdown_contMDiff i j n)

theorem ruling_contMDiff (n : WithTop ℕ∞) : ContMDiff 𝓘(ℂ,Coord) 𝓘(ℂ) n ruling :=
  contMDiff_of_affineParam _ n (fun i j => affineParam_ruling_contMDiff i j n)

/-- The product parametrization is analytic everywhere. -/
theorem localParam_contMDiff (i : Fin 2) (n : WithTop ℕ∞) :
    ContMDiff productModel 𝓘(ℂ,Coord) n (localParam i) := by
  intro q
  obtain ⟨j,s,hs⟩ := ProjectiveLine.charts_cover q.1
  have hj : q.1 ∈ ProjectiveLine.chartSet j := ⟨s,hs.symm⟩
  have hc := ((ProjectiveLineBundle.coordinates_contMDiffOn j n).contMDiffAt
    ((ProjectiveLine.chartSet_isOpen j).mem_nhds hj)).comp q
      (show ContMDiffAt productModel 𝓘(ℂ) n Prod.fst q from contMDiffAt_fst)
  have hh := (affineParam_contMDiff i j n).contMDiffAt.comp q
    (hc.prodMk_space contMDiffAt_snd)
  apply hh.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.eventually
    ((ProjectiveLine.chartSet_isOpen j).mem_nhds hj)] with q' hq'
  exact congrArg (fun p => localParam i (p,q'.2)) (ProjectiveLine.param_coordinates j q'.1 hq').symm

/-- The inverse product coordinates are analytic on the actual ruling open set. -/
theorem localCoordinates_contMDiffOn (i : Fin 2) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ,Coord) productModel n (localCoordinates i) (rulingChart i) := by
  intro q hq
  have hf := (fiberDirection_contMDiffAt i n (blowdown q)
    (fiberProjection_rep_nonzero i q hq)).comp q (blowdown_contMDiff n).contMDiffAt
  have ht := ((ProjectiveLineBundle.coordinates_contMDiffOn i n).contMDiffAt
    ((ProjectiveLine.chartSet_isOpen i).mem_nhds hq)).comp q (ruling_contMDiff n).contMDiffAt
  exact (hf.prodMk ht).contMDiffWithinAt

/-- A certified analytic local product on the actual one-point incidence manifold. -/
theorem ruling_local_analytic_product (i : Fin 2) :
    IsOpen (rulingChart i) ∧
      ContMDiff productModel 𝓘(ℂ,Coord) ω (localParam i) ∧
      ContMDiffOn 𝓘(ℂ,Coord) productModel ω (localCoordinates i) (rulingChart i) ∧
      (∀ q, localCoordinates i (localParam i q) = q) ∧
      (∀ q ∈ rulingChart i, localParam i (localCoordinates i q) = q) :=
  ⟨rulingChart_isOpen i,localParam_contMDiff i ω,localCoordinates_contMDiffOn i ω,
    localCoordinates_localParam i,localParam_localCoordinates i⟩

end
end FailureOfSemipositiveMetricExtension.Hisamoto
