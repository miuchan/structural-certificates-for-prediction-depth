# Amplekso de la formaligo

[English](../../../docs/requirements.md) · [简体中文](../../zh-CN/docs/requirements.md) · [日本語](../../ja/docs/requirements.md) · **Esperanto**

La projekto pruvas en Lean 4 strukturajn kriteriojn pri la prognoza profundo de dinamikaj sistemoj. Ĝi kovras konkretajn maŝinmodelojn, P-kompletecon de CVP kaj fermitecon de unuforma NC sub reduktoj. La tabelo listigas la ĉefajn kriteriojn, kompleksecajn fundamentojn kaj ekzemplojn. La defaŭlta enirmodulo kovras ĉiujn listigitajn modulojn.

| Postulo | Formala atesto | Stato |
| --- | --- | --- |
| Diskreta evoluo kaj observado | `Dynamics.predict` kaj la difino de OR sur la senfina entjera krado | Realigita |
| Cirkvitoj kun limigita enira grado, arbitra drataro kaj komunaj subcirkvitoj | `BoundedCircuit`, `LayeredNetwork`, `BinaryCircuit` kaj semantika traduko | Realigita |
| Enirlongo, fiksa grandobuĝeto, unuformeco je familia nivelo kaj profunda difino | `Families.Policy`, `Admissible`, `RealizesProfile`, `intrinsicDepth`, plus norma `UniformNC` kaj konkretaj generiloj por OR kaj A | Kompilita. La limoj de ambaŭ tavoloj estas dokumentitaj. |
| A. Semantiko kaj operacinombro de duuma ripeta kvadratigo, kompaktaj mezaj prezentoj | `FastComposition` | Realigita |
| A. Konstruo de prognoza cirkvito el primitivaj cirkvitoj kaj baroj por profundo, pordegonombro kaj priskribogrando | `CompiledComposition.Implementation` | Realigita |
| A. Kondiĉoj nur pri la efektive uzataj prezentoj kaj kunmetoj | `PathComposition`, kun ekzemplo strikte pli malforta ol la tutmonda kondiĉo | Kompilita per Lean 4.36 |
| A. Senfina tutmonda statspaco kun finia enira fenestro | `EncodedPathComposition` | Kompilita per Lean 4.36 |
| A. Efektiva logspaca unuformeco de ĝenerala prognozilo el generiloj por la primitivaj familioj | `Complexity/UniformComposition`, kun kanona tempobitĉeno, kompilado de primitivoj al kompleta cirkvitgenerilo kaj pruvo de polinoma grando | Kompilita per Lean 4.36 kaj sendepende kontrolita pri aksiomoj |
| Lineara sistemo super finia kampo kaj plurlogaritma profundobaro | `Linear`, `LinearSize` | Realigita |
| B. Unuma tempokodado, simula redukto kaj kondiĉa transigo de malfacileco | `Hardness.SimulationWitness` | Realigita parametrohava meta-teoremo |
| Normaj logspacaj reduktoj kaj fermiteco sub kunmeto | `Complexity/Logspace.lean` uzas konkretajn maŝinojn kun finia nombro da bendoj kaj pruvitan rekomputan kompililon. | Kompilita per Lean 4.36 |
| P-kompleteco de norma CVP | `Complexity/CVP.lean` uzas kodadon, taksadan maŝinon kaj redukton per Turing-maŝinaj komputtabeloj. | Kompilita per Lean 4.36 kaj kontrolita pri aksiomoj |
| Norma komplekseca versio de B | `Complexity/StandardHardness.lean` uzas konkretan CVP-kompletecon kaj fermitecon. | Kompilita per Lean 4.36 |
| Difino de norma unuforma NC kaj inkluzivo en P | `Complexity/UniformNC.lean` | Kompilita per Lean 4.36 |
| Fermiteco de unuforma NC sub arbitraj logspacaj reduktoj | `NCClosure`, kun konfiguraciaj grafeoj, paralela atingebleco, flua grupa generado kaj elekto de ŝanĝiĝemlonga eliro | Kompilita per Lean 4.36 kaj kontrolita pri aksiomoj |
| Kondiĉa malfacileco sub disiĝo de P kaj NC | `SimulationWitness.prediction_not_uniformNC` kun eksplicita supozo `P ≠ NC` | Kompilita per Lean 4.36 kaj kontrolita pri aksiomoj |
| Maŝinnivela unuformeco kaj preciza optimuma profundo de la konkreta OR-cirkvitfamilio | `UniformOROptimal.exact_uniform_prediction` | Kompilita per Lean 4.36 kaj kontrolita pri aksiomoj |
| C. Profundobaro el nombro de esencaj variabloj kaj kontrolebla finia atestilo | `DependencyWitness` kaj malsupraj baroj por cirkvitoj kaj retoj | Realigita |
| Preciza optimuma profundo kaj lineara supra grandobaro por la OR-ĉela aŭtomato | `ORAutomaton.exact_prediction_depth` | Realigita |
| Disvastiĝa malsupra baro por geometrie limigitaj prognoziloj | `Geometry.local_layers` kaj la geometria baro por OR | Realigita |
| Limo de la metodo kalkuli enirajn dependecojn | `dependency_method_limit` | Realigita |
| Tempo nul, malplena eniro, unuopa eniro kaj konkretaj linearaj ekzemploj | `Examples` | Realigita |
| Nelineara regulfamilio kun fiksita regado, logaritma profundo kaj unuforma NC¹ | `FrozenPascal.GuardRules`, `FrozenPascal.UniformLanguage`, `FrozenPascal.LowerBound` | Kompilita per Lean 4.36 kaj kontrolita pri aksiomoj |
| Necesa kaj sufiĉa kondiĉo por konstanta profundo kun fiksita regado kaj klasifiko por ĉiu tempo | `bounded_prediction_depth_iff` kaj la malsupra baro por variaj gardoj en `FrozenPascal/Classification.lean`, plus profundobaroj laŭ la nombro de unubitoj en `FrozenPascal/HomogeneousPascal.lean` | Vidu la [kontrolregistron](verification.md) |
| Rulebla regulklasifiko kaj efektiva unuforma profundoklasifiko | `classify_eq_iff`, `uniform_depth_classification`, `predictionLanguage_mem_uniformNC_zero_iff` | Vidu la [kontrolregistron](verification.md) |
| Strikta kompilado de la tuta projekto, transitiva aksioma kontrolo kaj negativa regresia testo | `scripts/check.sh`, `Audit.lean`, `scripts/check_audit.py`, `.github/workflows/lean.yml` | Vidu la [kontrolregistron](verification.md) |
