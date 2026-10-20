import FailureOfSemipositiveMetricExtension.CentralAuxiliaryZeroSets

/-! The explicit projective-line parametrization of the central strict transform
of z=0.  All points, including the three exceptional intersection points, are
constructed inside the actual incidence fibre. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

def lineEmbedding : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun v := ![v 0,v 1,0]
  map_add' u v := by ext i; fin_cases i <;> simp
  map_smul' a v := by ext i; fin_cases i <;> simp

theorem lineEmbedding_injective : Function.Injective lineEmbedding := by
  intro u v h
  ext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1

/-- The genuine quotient-level inclusion [x:y]↦[x:y:0]. -/
def lineBase : Direction → PlanePoint := Projectivization.map lineEmbedding lineEmbedding_injective

theorem lineBase_injective : Function.Injective lineBase :=
  Projectivization.map_injective lineEmbedding lineEmbedding_injective

@[simp] theorem lineBase_param (i : Fin 2) (s : ℂ) :
    lineBase (FailureOfSemipositiveMetricExtension.ProjectiveLine.param i s) =
      FailureOfSemipositiveMetricExtension.ProjectivePlane.param i.castSucc (s,0) := by
  fin_cases i <;> rfl

theorem lineBase_not_chart_two (d : Direction) :
    lineBase d ∉ FailureOfSemipositiveMetricExtension.ProjectivePlane.chartSet 2 := by
  obtain ⟨i,s,rfl⟩ := FailureOfSemipositiveMetricExtension.ProjectiveLine.charts_cover d
  rw [lineBase_param,FailureOfSemipositiveMetricExtension.ProjectivePlane.param_mem_chartSet_iff]
  fin_cases i <;> simp [FailureOfSemipositiveMetricExtension.ProjectivePlane.overlap,FailureOfSemipositiveMetricExtension.ProjectivePlane.vector,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]

def lineDirections (d : Direction) (r : Fin 4) : Direction :=
  if r = 3 then d else FailureOfSemipositiveMetricExtension.ProjectiveLine.param 0 0

theorem line_incidence (d : Direction) (r : Fin 4) :
    Incidence (lineBase d) (lineDirections d r) r 0 := by
  induction d using Projectivization.ind with
  | h v hv =>
    change Incidence (Projectivization.mk ℂ (lineEmbedding v) _) (lineDirections _ r) r 0
    rw [incidence_mk_iff]
    fin_cases r
    · change pairMap 0 0 (lineEmbedding v) ∈ (FailureOfSemipositiveMetricExtension.Blowup.lineX 0).submodule
      rw [FailureOfSemipositiveMetricExtension.Blowup.lineX,Projectivization.submodule_mk,Submodule.mem_span_singleton]
      refine ⟨v 1,?_⟩
      ext i; fin_cases i <;> simp [pairMap,pair,lineEmbedding,FailureOfSemipositiveMetricExtension.Blowup.vectorX]
    · change pairMap 1 0 (lineEmbedding v) ∈ (FailureOfSemipositiveMetricExtension.Blowup.lineX 0).submodule
      rw [FailureOfSemipositiveMetricExtension.Blowup.lineX,Projectivization.submodule_mk,Submodule.mem_span_singleton]
      refine ⟨v 0,?_⟩
      ext i; fin_cases i <;> simp [pairMap,pair,lineEmbedding,FailureOfSemipositiveMetricExtension.Blowup.vectorX]
    · change pairMap 2 0 (lineEmbedding v) ∈ (FailureOfSemipositiveMetricExtension.Blowup.lineX 0).submodule
      rw [FailureOfSemipositiveMetricExtension.Blowup.lineX,Projectivization.submodule_mk,Submodule.mem_span_singleton]
      refine ⟨v 1-v 0,?_⟩
      ext i; fin_cases i <;> simp [pairMap,pair,lineEmbedding,FailureOfSemipositiveMetricExtension.Blowup.vectorX]
    · change pairMap 3 0 (lineEmbedding v) ∈ (Projectivization.mk ℂ v hv).submodule
      have he : pairMap 3 0 (lineEmbedding v) = v := by ext i; fin_cases i <;> rfl
      rw [he,Projectivization.submodule_mk]
      exact Submodule.mem_span_singleton_self v

/-- The strict-transform point with directions [1:0],[1:0],[1:0],[x:y]. -/
def lineParam (d : Direction) : Fiber 0 := ⟨(lineBase d,lineDirections d),line_incidence d⟩

@[simp] theorem lineParam_blowdown (d : Direction) : FixedFiber.blowdown 0 (lineParam d) = lineBase d := rfl
@[simp] theorem lineParam_direction (d : Direction) (r : Fin 4) :
    FixedFiber.direction 0 r (lineParam d) = lineDirections d r := rfl
@[simp] theorem lineParam_direction_three (d : Direction) : FixedFiber.direction 0 3 (lineParam d) = d := by
  simp [lineParam_direction,lineDirections]

theorem lineParam_injective : Function.Injective lineParam := by
  intro d d' h
  simpa using congrArg (FixedFiber.direction 0 3) h

/-- The selected direction in each actual fibre blow-up chart. -/
theorem fixedParam_selected_direction (t : ℂ) (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) :
    FixedFiber.direction t r (FixedFiber.param t r e q) = FailureOfSemipositiveMetricExtension.ProjectiveLine.param e q.2 := by
  change directions (chartParam r e (q,t)) r = _
  simp only [chartParam,localLift_direction,localParam_direction]

/-- Any blow-up chart meeting this explicit projective line is one of the first
three X-charts, and its slope coordinate is zero. -/
theorem lineParam_chart_data (d : Direction) (r : Fin 4) (e : Fin 2)
    (hp : lineParam d ∈ FixedFiber.source 0 r e) :
    r ≠ 3 ∧ e = 0 ∧ (FixedFiber.coordinates 0 r e (lineParam d)).2 = 0 := by
  have hi := (mem_chartSource_iff r e (FixedFiber.inclusion 0 (lineParam d))).mp hp
  have hr : r ≠ 3 := by
    intro hr
    subst r
    exact lineBase_not_chart_two d hi.1
  have he : e = 0 := by
    have hd : FailureOfSemipositiveMetricExtension.ProjectiveLine.param 0 0 ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet e := by
      simpa [directions,FixedFiber.inclusion,lineParam,lineDirections,hr] using hi.2.1
    fin_cases e
    · rfl
    · have hz := (FailureOfSemipositiveMetricExtension.ProjectiveLine.param_mem_chartSet_iff 0 1 0).mp hd
      exact False.elim (hz rfl)
  have hq := FixedFiber.param_coordinates 0 r e (lineParam d) hp
  have hd := congrArg (FixedFiber.direction 0 r) hq
  rw [fixedParam_selected_direction,lineParam_direction] at hd
  simp only [lineDirections,if_neg hr,he] at hd
  exact ⟨hr,he,by simpa only [he] using FailureOfSemipositiveMetricExtension.ProjectiveLine.param_injective 0 hd⟩

/-- Every explicit projective-line point is a zero of the actual section ℓ. -/
theorem ellSection_lineParam_zero (d : Direction) : sectionValue ellSection (lineParam d) = 0 := by
  obtain ⟨⟨r,e⟩,hp⟩ := FixedFiber.charts_cover 0 (lineParam d)
  obtain ⟨hr,he,hs⟩ := lineParam_chart_data d r e hp
  have hz := ellDivisionData.quotientSection_zero_iff_coordinates r e (lineParam d) hp
  apply hz.mpr
  change ellLocalCoefficient r e (FixedFiber.coordinates 0 r e (lineParam d)) = 0
  simp only [ellLocalCoefficient,if_neg hr,if_pos he]
  exact hs

/-- The actual closed zero-locus subtype; its topology remains the inherited topology. -/
def EllCurve := {p : Fiber 0 // sectionValue ellSection p = 0}

def lineCurveParam (d : Direction) : EllCurve := ⟨lineParam d,ellSection_lineParam_zero d⟩

def lineCurveInverse (p : EllCurve) : Direction := FixedFiber.direction 0 3 p.val

@[simp] theorem lineCurveInverse_param (d : Direction) : lineCurveInverse (lineCurveParam d) = d :=
  lineParam_direction_three d


/-- The direction [x:y] determined by the radial coordinate in each X-chart. -/
def lineChartDirection (r : Fin 4) (s : ℂ) : Direction :=
  match r with
  | 0 => FailureOfSemipositiveMetricExtension.ProjectiveLine.param 0 s
  | 1 => FailureOfSemipositiveMetricExtension.ProjectiveLine.param 1 s
  | 2 => FailureOfSemipositiveMetricExtension.ProjectiveLine.param 0 (1+s)
  | 3 => FailureOfSemipositiveMetricExtension.ProjectiveLine.param 0 s

/-- A zero-slope point in any of the first three X-charts is the explicit line point. -/
theorem lineParam_eq_of_chart (p : Fiber 0) (r : Fin 4)
    (hp : p ∈ FixedFiber.source 0 r 0) (hr : r ≠ 3)
    (hs : (FixedFiber.coordinates 0 r 0 p).2 = 0) :
    lineParam (lineChartDirection r (FixedFiber.coordinates 0 r 0 p).1) = p := by
  let q := FixedFiber.coordinates 0 r 0 p
  let d := lineChartDirection r q.1
  have hq := FixedFiber.param_coordinates 0 r 0 p hp
  have hb : lineBase d = FixedFiber.blowdown 0 p := by
    conv_rhs => rw [← hq]
    change lineBase (lineChartDirection r q.1) = affineBase r 0 (Blowup.projection (localParam 0 q))
    have hs' : q.2 = 0 := hs
    fin_cases r
    · simp [lineChartDirection,lineBase_param,affineBase_eq_param,baseChart,baseCoordinates,
        localParam,Blowup.projection,Blowup.X,hs']
      rfl
    · simp [lineChartDirection,lineBase_param,affineBase_eq_param,baseChart,baseCoordinates,
        localParam,Blowup.projection,Blowup.X,hs']
      rfl
    · simp [lineChartDirection,lineBase_param,affineBase_eq_param,baseChart,baseCoordinates,
        localParam,Blowup.projection,Blowup.X,hs']
      rfl
    · exact (hr rfl).elim
  apply FixedFiber.inclusion_injective 0
  change FixedFiber.inclusion 0 (lineParam d) = FixedFiber.inclusion 0 p
  apply total_ext (p := FixedFiber.inclusion 0 (lineParam d)) (q := FixedFiber.inclusion 0 p) hb _ rfl
  funext j
  by_cases hj : j = r
  · subst j
    change lineDirections d r = FixedFiber.direction 0 r p
    have hd := congrArg (FixedFiber.direction 0 r) hq
    rw [fixedParam_selected_direction] at hd
    simpa only [lineDirections,if_neg hr,hs] using hd
  · apply directions_eq_away (FixedFiber.inclusion 0 (lineParam d)) (FixedFiber.inclusion 0 p) j hb rfl
    change lineBase d ≠ centre j 0
    rw [hb]
    exact ((mem_chartSource_iff r 0 (FixedFiber.inclusion 0 p)).mp hp).2.2 j hj

/-- The constructed projective line exhausts the entire actual zero locus. -/
theorem lineParam_surjective_zero (p : Fiber 0) (hz : sectionValue ellSection p = 0) :
    ∃ d : Direction, lineParam d = p := by
  obtain ⟨⟨r,e⟩,hp⟩ := FixedFiber.charts_cover 0 p
  have hl := ellDivisionData.quotientSection_zero_iff_coordinates r e p hp
  have hs : ellLocalCoefficient r e (FixedFiber.coordinates 0 r e p) = 0 := hl.mp hz
  have hr : r ≠ 3 := by intro hr; simp [ellLocalCoefficient,hr] at hs
  have he : e = 0 := by by_contra he; simp [ellLocalCoefficient,hr,he] at hs
  subst e
  simp only [ellLocalCoefficient,if_neg hr,if_pos rfl] at hs
  exact ⟨lineChartDirection r (FixedFiber.coordinates 0 r 0 p).1,lineParam_eq_of_chart p r hp hr hs⟩

@[simp] theorem lineCurveParam_inverse (p : EllCurve) : lineCurveParam (lineCurveInverse p) = p := by
  obtain ⟨d,hd⟩ := lineParam_surjective_zero p.val p.property
  apply Subtype.ext
  change lineParam (FixedFiber.direction 0 3 p.val) = p.val
  rw [← hd,lineParam_direction_three]

/-- An actual set equivalence, with inverse given by the fourth direction coordinate. -/
def lineCurveEquiv : Direction ≃ EllCurve where
  toFun := lineCurveParam
  invFun := lineCurveInverse
  left_inv := lineCurveInverse_param
  right_inv := lineCurveParam_inverse

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
