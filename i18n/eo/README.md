# Strukturaj atestiloj pri la prognoza profundo de dinamikaj sistemoj

[English](../../README.md) · [简体中文](../zh-CN/README.md) · [日本語](../ja/README.md) · **Esperanto**

La esplora demando estas, kiuj kontroleblaj strukturaj kondiĉoj pri dinamika sistemo donas barojn por la cirkvita profundo de prognozo. Prognozproblemon difinas la evoluregulo, observado, enirkodado kaj permesataj cirkvitoj. La projekto kontrolas tri reuzeblajn kriteriojn en Lean 4.

La nuna artikolo de Amamiya Miu traktas familion de unuflankaj ĉelaj aŭtomatoj kun fiksita regado. La regvortoj povas varii laŭ pozicio. Kun fiksitaj regvortoj la datuma trako evoluas lineare, kaj nombrado de vojoj reduktas prognozon al prefiksaj statistikoj kaj koeficienta pareco. La komparo kun evoluanta regado traktas kaj unuopan datuman vojon kaj regulojn kun du branĉoj. La angla eldono estas la ĉefa. [Artikolo en PDF](../../paper/structural-certificates.eo.pdf) · [Typst-fonto](../../paper/structural-certificates.eo.typ) · [Komparo kun la literaturo](docs/literature.md)

## Prognozo per maldensaj korektoj

Ĉiu postresta bito komparas la efektivan ĝisdatigon kun tiu de fiksa lineara referenco en la plena dependokeglo. Lean kontrolas la nombradon kaj la unuformajn NC¹-rezultojn por konstanta buĝeto ĉe nekonataj pozicioj kaj por logaritme longa listo de eblaj pozicioj. La reigebla tritraka kolizia ekzemplo havas ĝuste tri postrestajn bitojn en la keglo por ĉiu pozitiva distanco. Lean ankaŭ kontrolas la tempordajn riparcirkvitojn por bitoj kaj tavoloj kun logspacaj generiloj, kaj la plenajn pelatajn respondojn por Pascal kaj libera transporto. La artikolo pruvas la pelatan respondon por ĉiu fiksa homogena duuma lineara regulo. [Esplora specifo](../../docs/sparse-corrections.md) · [Lean-enirejo](../../PredictionDepth/SparseCorrections.lean)

Por la fiksa tritraka kolizia regulo, ĉiu komenca fenestro kun maksimume du partikloj havas maksimume du restaĵajn bitojn. Aparta malsupra baro per esencaj eniroj donas la optimuman profundordon $\Theta(\log(T+1))$ sub tiu promeso. Por OR kun Pascal kiel referenco, la komenca fenestro kun ĉiuj bitoj egalaj al unu havas $T^2$ restaĵajn bitojn, dum prognozo por ĉiuj eniroj havas minimuman profundon $\lceil\log_2(T+1)\rceil$.

## Profundoklasifiko de la reguloj kun fiksita regado

Fiksu la larĝon $q$ de regvorto kaj du gardajn funkciojn por restado kaj salto. Ĉiu prognozo ricevas eksplicite la regvortojn kaj datumajn bitojn de la ĉeloj $0,\ldots,T$. La valida enirlongo do estas $n=(q+1)(T+1)$ kaj determinas la tempon $T$. La tabelo distingas malsuprajn barojn por arbitraj du-eniraj pordegoj, la minimuman profundon de De Morgan je ĉiu tempo kaj la supran baron de la kontrolita unuforma familio. Arbitra drataro kaj komunaj subcirkvitoj estas permesataj.

| Gardaj funkcioj | Prognoza profundo |
| --- | --- |
| Salto ĉiam malpermesita | Konstanta profundo. Je pozitiva tempo sufiĉas legi la restogardon kaj la datuman biton ĉe la origino. |
| Salto ĉiam permesita, restado ĉiam malpermesita | Nula profundo. La cirkvito rekte legas la datuman biton de ĉelo $T$. |
| Nekonstanta saltogardo, aŭ konstante permesita salto kun nekonstanta restogardo | $\Theta(\log(T+1))$. Almenaŭ $T+1$ esencaj enirbitoj donas la malsupran baron. La gardoj AND kaj OR estas ekzemplo. |
| Salto kaj restado ĉiam permesitaj | Estu $`p`$ la nombro de unubitoj de $`T`$. La minimuma profundo kun du-enira XOR estas $`p`$. Kun NOT nombrata kiel unu tavolo, la minimuma De Morgan-profundo estas nulo je $`T=0`$ kaj $`2p+1`$ je $`T>0`$. La supra baro de la unuforma generilo estas $`3p`$. |

`classify` trairas la finiajn regvortojn laŭ prefiksoj kaj ĉesigas la nunan provon pri konstanteco ĉe la unua kontraŭekzemplo, sen konstrui kompletan liston de regvortoj. Elĉerpa provo ankoraŭ povas viziti $`2^q`$ vortojn. `classify_eq_iff` pruvas, ke la rezulto ekvivalentas al la kondiĉoj en la tabelo. Por ĉiu fiksita paro de gardoj, `uniform_depth_classification` donas unu logspac-unuforman cirkvitfamilion de polinoma grando, kiu realigas la supran profundobaron de la koncerna branĉo. Tio inkluzivas la baron de $`3p`$ tavoloj por la homogena Pascal-regulo. La lingvo apartenas al unuforma NC⁰ ĝuste kiam la regulo estas en unu el la unuaj du branĉoj. [Matematika argumento pri fiksita regado](docs/frozen-pascal.md)

## Transportata regado kiel struktura komparo

Fiksu $`u,v\in\{0,1\}`$. Ĉiu paŝo aplikas $`c'_i=c_{i+u}`$ kaj $`d'_i=c_i\land d_{i+v}`$. La eniro enhavas eksplicite la bitojn de ambaŭ trakoj ĉe $`0,\ldots,T`$. Je tempo nul la antaŭdiro rekte legas datuman biton, kun nula profundo. Je pozitiva tempo egalaj rapidoj postulas legi unu komencan regbiton kaj unu datuman biton, do la preciza profundo estas 1. Kun malsamaj rapidoj la prognozo legas $`T`$ komencajn regbitojn kaj unu datuman biton, kun preciza profundo $`\lceil\log_2(T+1)\rceil`$. Lean konstruas AND-arbon kun lineara nombro da pordegoj kaj pruvas kongruan malsupran baron por du-eniraj cirkvitoj kun komunaj subcirkvitoj. La rezulto por ĉiu tempo montras, ke moviĝanta regado povas postuli logaritman profundon eĉ se la datumo restas surloke. [Semantiko kaj profundo de transportata regado](../../PredictionDepth/TransportedControl.lean)

Kun unuforme ŝoviĝanta rega trako oni povas konservi ambaŭ branĉojn por restado kaj salto. Lean kontrolas, ke speguli la koordinatojn laŭ la moviĝo fiksas la regadon kaj interŝanĝas la du gardojn. Rekonekti la enirojn de la finia fenestro ebligas reuzi la prognozan cirkviton por fiksita regado kun la sama nombro da pordegoj kaj sen pligrandigo de la profundo. [Moviĝanta referenca kadro kaj fenestra drataro](../../PredictionDepth/TransportedBranching.lean)

Por $`c'_i=c_i\oplus c_{i+1}`$ kaj $`x'_i=c_ix_i\oplus x_{i+1}`$, la prefiksaj nombroj de la fiksa modelo ne determinas la koeficientojn. La koeficiento de datumbito $`T`$ estas 1. Por $`k<T`$ ĝi estas la komuna Pascal-pareco $`Q_T=c_0(T)\oplus c_T(0)`$ multiplikita per la indikilo, ke la rega sufikso $`c_{k+1}(0),\ldots,c_{T-1}(0)`$ estas tutnula. Lean kontrolas la koeficientan formulon. Lean kontrolas la prognozilon, kiun la komuna kompililo de ordigitaj blokresumoj generas el tri-bita resumo. La cirkvitfamilio estas logspac-unuforma, kun lineara nombro da pordegoj kaj logaritma profundo. Por ĝustaj cirkvitoj kun arbitra drataro kaj maksimume du eniroj ĉe ĉiu pordego, Lean ankaŭ pruvas la malsupran profundobaron $`\lceil\log_2(T+1)\rceil`$. [Lean-formulo](../../PredictionDepth/AdditiveBranching.lean) · [Unuforma prognozilo](../../PredictionDepth/AdditiveBranching/Summary.lean) · [Malsupra profundobaro](../../PredictionDepth/AdditiveBranching/LowerBound.lean)

## Formaliga infrastrukturo

La tri kriterioj kompilas primitivajn cirkvitojn kun rimedobaroj al prognoziloj (A), transigas kompleksecan malfacilecon per konkretaj simulaj atestiloj (B) kaj derivas profundobarojn por limigita enira grado el la nombro de esencaj eniroj (C). La norma tavolo ligas konkretajn Turing-maŝinojn, CVP-kompletecon kaj la fermitecon de unuforma NC sub reduktoj. La OR-ĉela aŭtomato ilustras precizan profundon kaj geometriajn limigojn. Matricoj super la dukorpa kampo ilustras la koston de kunmeto. [Postularo](docs/requirements.md) · [Dependecoj kaj maŝinmodeloj](docs/dependencies.md) · [Kontrolregistro](docs/verification.md)

## Reproduktado

`lean-toolchain` fiksas Lean al `v4.36.0-rc2` kaj `lake-manifest.json` fiksas ĉiujn dependecojn. La normaj kompleksecaj fundamentoj devenas de [cslib-frontier](https://github.com/cslib-community/cslib-frontier/tree/3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d), en la enmeto `3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d`. Ĝia dependecgrafeo determinas la versiojn de CSLib kaj Mathlib.

```sh
lake exe cache get  # Nedevige, por elŝuti la kompilkaŝmemoron de dependecoj.
./scripts/check.sh
```

`scripts/check.sh` unue faras striktan kompiladon, poste kontrolas la transitivajn importojn de la kompilita enirmodulo kaj la aksiomajn dependecojn, kaj rulas la regresiajn testojn de ambaŭ kontroloj. La kontrolo elektas deklarojn laŭ la projekto-modulo en kiu ili estas difinitaj kaj permesas nur `propext`, `Classical.choice` kaj `Quot.sound`. GitHub Actions rulas la saman skripton por la enmeto, kiu ekigas la laborfluon. [Kontrolprocedo](docs/verification.md)

La angla artikolo uzas Typst 0.15.1 kaj la tiparojn enkonstruitajn en la kompililo. Por rekrei la anglan PDF-dosieron, rulu jenon el la deponeja radiko.

```sh
typst compile --ignore-system-fonts --creation-timestamp 1794268800 \
  paper/structural-certificates.typ paper/structural-certificates.pdf
```

Por kompili ĉiujn kvar versiojn, metu la statikajn SC- kaj JP-tiparojn Regular kaj Bold en unu dosierujon kaj rulu la jenan komandon per Typst 0.15.1 el la deponeja radiko. [Noto Serif CJK 2.003](https://github.com/notofonts/noto-cjk/releases/tag/Serif2.003)

```sh
./scripts/build-papers.sh /path/to/cjk-fonts
```

## Ĉefaj teoremoj kaj kodo

| Temo | Modulo kaj ĉefaj deklaroj |
| --- | --- |
| Evoluo, observado kaj kunmeto de lokaj mapoj | `Dynamics.lean` · `predict`, `Geometry.Local.comp`, `local_layers` |
| Cirkvitoj kun limigita enira grado, komunaj subcirkvitoj en DAG kaj dependecbaroj | `Circuit.lean` · `essential_count_le_pow`, `DependencyWitness` |
| Preciza semantiko kaj operacinombro de ripeta kvadratigo | `FastComposition.lean` · `compile_exponent`, `compile_operations`, `fast_prediction_correct` |
| A. Kompili prognozilon el efektivaj primitivaj cirkvitoj | `EncodedPathComposition.lean` · `EncodedPathImplementation.compiled_predictor_correct` kaj rimedobaroj. `CompiledComposition.lean` konservas la tutmonde ĝustan specialan kazon. |
| A. Efektiva unuforma generilo kaj norma NC-korolario | `Complexity/UniformComposition.lean` · `UniformRegisterWitness.uniform`, `depth_le_costs`, `mem_uniformNCLevel_of_cost` |
| Semantika ligo inter du cirkvitaj prezentoj | `CircuitInterop.lean` · `BinaryCircuit.unfoldOutput_eval` |
| Preciza optimuma profundo de la OR-ĉela aŭtomato | `ORAutomaton.lean`. `exact_uniform_prediction` en `Complexity/UniformOROptimal.lean` ankaŭ enhavas la efektivan unuforman generilon. |
| Fiksita enirlongo, grandobuĝeto, familiaj kondiĉoj kaj profundo | `Families.lean` · `Policy`, `Admissible`, `RealizesProfile`, `intrinsicDepth` |
| Konkretaj matricaj cirkvitoj super la dukorpa kampo | `Linear.lean`, `LinearSize.lean` |
| B. Parametra meta-teoremo pri simula redukto | `Hardness.lean`. [Detalaj kondiĉoj](docs/hardness.md) |
| B. Konkretaj maŝinoj kaj norma CVP-fundamento | `Complexity/Logspace.lean`, `CVP.lean`, `StandardHardness.lean` |
| Fermiteco de norma NC kaj kondiĉa baro al rapida prognozo | `Complexity/NCClosure.lean` · `uniformNC_closed_logspace`, `SimulationWitness.prediction_not_uniformNC` |
| Paralela atingebleco, unuforma NC² kaj flua generado | `Complexity/Reachability.lean`, `UniformReachability.lean`, `LogspaceBatch.lean` |
| Limo de la metodo kalkuli informajn dependecojn | `DependencyGrowth.lean` · `dependency_method_limit` |
| Unuflanka regulfamilio kun fiksita regado | `iterate_data` en `FrozenPascal/Semantics.lean` kaj `predictionLanguage_mem_uniformNC_one` en `FrozenPascal/UniformLanguage.lean` |
| Profundoklasifiko por fiksita regado | `bounded_prediction_depth_iff` kaj `varyingGuard_prediction_depth_lower_bound` en `FrozenPascal/Classification.lean`. `pascalSupport_card` kaj la profundobaroj laŭ la nombro de unubitoj en `FrozenPascal/HomogeneousPascal.lean`. |
| Minimuma profundo de la homogena Pascal-regulo je ĉiu tempo | `homogeneousNativeXorPrediction_depth`, `homogeneous_prediction_deMorgan_exact_depth`, `homogeneous_prediction_deMorgan_depth_lower_bound` |
| Rulebla klasifikilo kaj unuforma profundoklasifiko | `classify_eq_iff` en `FrozenPascal/Classification.lean`. `uniform_depth_classification` kaj `predictionLanguage_mem_uniformNC_zero_iff` en `FrozenPascal/UniformClassification.lean`. |
| Esencaj eniroj kaj preciza profundo ĉe transportata regado | `TransportedControl.lean` · `iterate_data_true_iff`, `essential_prediction_iff`, `exact_prediction_depth`, `constant_depth_iff` |
| Moviĝanta referenca kadro kaj cirkvita reuzo je ĉiu tempo | `TransportedBranching.lean`, `reverseFrame_iterate`, `prediction_correct`, `prediction_depth`, `prediction_size` |
| Ruleblaj randokazoj kaj ekzemplokontroloj | `Examples.lean` |

### A. Rapide kunmeteblaj prezentoj

`Realization` postulas, ke la identa prezento, la unupaŝa prezento kaj kunmeto respektu la veran funkcian semantikon. `compile T` estas rulebla duuma programo de ripeta kvadratigo. Kvadratigo reuzas ekzistantajn registrojn, kaj la nombro de kunmetoj estas maksimume

```math
2\lceil\log_2(T+1)\rceil.
```

`EncodedPathImplementation` provizas bitkodadon de larĝo `L` kaj efektivajn du-enirajn buleajn cirkvitojn por pravalorizo, kunmeto kaj observado. La ĝusteco de kunmeto estas postulata laŭ la efektive plenumata vojo. Prezentoj ekster tiu vojo ne bezonas havi kodon de larĝo `L`. La tutmonda statspaco povas esti senfina. Specifita mapo enigas la finian bitĉenon en tiun spacon. La kompililo pruvas, ke la eliro estas precize $`O(F^T(\mathrm{input}(x)))`$, kaj pruvas

```math
d_{\rm pred}\le d_{\rm init}
 +2\lceil\log_2(T+1)\rceil d_{\rm comp}+d_{\rm obs}.
```

La baro por la nombro de pordegoj havas la saman adician formon. Alia baro por la grandeco de la priskribo inkluzivas la dratliston kaj la kunmetan sintakson. La formulo eksplicite enkalkulas la koston de pravalorizo. La kodado povas konservi ĝuste la informon bezonatan por la observado, do injektiveco ne estas postulata. La pli forta tutmonda `Implementation` estas speciala kazo de la voja kriterio kun pruvita konvertado.

La unuforma versio `UniformRegisterWitness` derivas generilon por la tuta prognoza cirkvitfamilio kaj polinoman grandobaron el efektivaj logspacaj generiloj por la kanona duuma tempo kaj kvar lokaj primitivaj cirkvitoj. La generilo relegas la tempan bitĉenon per indicoj kaj povas trakti grandan $`T`$ sen konservi ĝian valoron sur la laborbendo. La kompililo normaligas la elirajn dratojn al kontinua intervalo kaj eksplicite enkalkulas unu tavolon de kopiaj pordegoj ĉe ĉiu stadio.

```math
d_{\rm uniform}\le\eta+1+
2\lceil\log_2(T+1)\rceil(\delta+1)+\epsilon.
```

Kiam $`\delta\ge1`$, sekvas la baro $`\eta+1+4\lceil\log_2(T+1)\rceil\delta+\epsilon`$. La membreco en norma unuforma NC sekvas kiam la tuta kostesprimo estas plurlogaritma rilate al la **efektiva enirlongo**. La eblo generi la duuman tempokodon en logaritma spaco sola estas nesufiĉa.

`Linear.implementation` kodas elementojn de la dukorpa kampo per po unu bito. Ĝi realigas matrican multiplikon per paralela AND-tavolo kaj ekvilibra XOR-redukto, kio donas

```math
d(T,n)\le
2\lceil\log_2(T+1)\rceil(\lceil\log_2 n\rceil+1)
 +(\lceil\log_2 n\rceil+1).
```

La nombro de pordegoj kaj la grandeco de la kompleta priskribo havas konkretajn polinomajn barojn. Kiam $`n\le(T+1)^k`$, validas ankaŭ la pruvita finia malegaleco

```math
d(T,n)\le3(k+1)(\lceil\log_2(T+1)\rceil+1)^2.
```

Por apliki la unuformecan kriterion oni provizu generilojn kaj semantikajn atestilojn por la konkretaj primitivoj kaj la komenca matricfamilio. La teoremo tiam derivas la unuformecon de la tuta prognoza familio. Lineareco de la individuaj matricoj sola estas nesufiĉa por unuforma generado de arbitre elektita familio.

### B. Malfacileco el simulado

La tempdemando estas kodita kiel $`1^T0x`$. La pruvo kovras ĝustecon de kodigo kaj malkodigo, injektivecon, malakcepton de nevalidaj demandoj kaj longobaron por la plena demando. Simula atestilo provizas mapon de la origina cirkvitinstanco al stato kaj tempo, kaj pruvas por ĉiuj instancoj, ke la prognozo egalas la cirkvitan respondon.

`Hardness` konservas reuzeblan parametritan version. `Complexity/StandardHardness` aplikas konkretan modelon de finiaj multbendaj Turing-maŝinoj, efektivajn logspacajn transduktojn kaj norman CVP-kompletecon. Tio forigas la abstraktajn premisojn pri la malfacileco de CVP kaj fermiteco sub reduktoj. P-kompleteco postulas kroman pruvon, ke la prognoza problemo de la specifa sistemo apartenas al P.

`NCClosure` pruvas, ke unuforma NC estas fermita sub ĝeneralaj logspacaj reduktoj, inkluzive de reduktoj kies elirlongo dependas de la enira enhavo. Kun simula atestilo, la eksplicita apartiga supozo $`P\ne NC`$ implicas, ke la prognoza problemo estas ekster unuforma NC. Tiu konkludo estas pri klasmembreco.

### C. Malsupra baro el informaj dependecoj

Esenca eniro havas du valorasignojn, kiuj povas malsami nur ĉe tiu koordinato kaj kiuj donas malsamajn elirojn. Por cirkvito de enira grado maksimume `b` kaj profundo maksimume `d`, validas

```math
m\le b^d,\qquad
\lceil\log_b m\rceil\le d\quad(b\ge2).
```

`DependencyWitness` enhavas finian koordinataron kaj distingantajn valorasignojn por ĉiu koordinato. La pruvo kovras tavoligitajn direktitajn senciklajn grafeojn kun arbitra reuzado de eliroj. Ĝi disvolvas la cirkviton nur por pruvi la malsupran baron, ĉar la disvolvita formulo povas kreski eksponente.

### La OR-ekzemplo kaj geometriaj limigoj

Sur la senfina entjera krado la regulo
$`F(x)_i=x_{i-1}\lor x_i\lor x_{i+1}`$ donas

```math
F^T(x)_0=\bigvee_{j=-T}^{T}x_j,
\qquad D(T)=\lceil\log_2(2T+1)\rceil.
```

La eniro havas precize `2*T+1` bitojn. Etendo ekster la intervalo estas senefika por la prognozo. La kerna modelo donas formulon kun optimuma profundo kaj lineara grando. La norma tavolo konstruas ankaŭ efektivan logspac-unuforman familion de cirkvitoj de De Morgan kun optimuma profundo. Ĝi uzas $`n\lceil\log_2 n\rceil`$ pordegojn ene de fiksita kvadrata buĝeto kaj havas kongruan malsupran baron por ĉiuj cirkvitoj de De Morgan kun komunaj subcirkvitoj. Ambaŭ konstruoj havas nulan profundon je $`T=0`$.

Unu ĝisdatiga rondo uzas OR de tri eniroj. Rekta realigo per pordegoj de maksimume du eniroj bezonas konstantan nombron da logikaj tavoloj por rondo. Fizika rondo kaj logika tavolo estas apartaj unuoj.

Se la spaca radiuso de ĉiu tavolo de la prognozilo estas maksimume `r` kaj la fora eniro efektive influas la eliron, validas $`T\le d\,r`$. La supozo limigas la geometrion de la drataro de la prognozilo. Por cirkvitoj kun arbitraj longdistancaj dratoj validas la antaŭa logaritma profundobaro.

## Matematikaj limoj

- `Nat.clog` donas la diskretan suprenrondigitan logaritmon, inkluzive de la kazoj kun nul aŭ unu eniro. Asimptota interpreto kun reela logaritmo uzas pozitivajn argumentojn.
- `intrinsicDepth` fiksas la enirlongon, la grandokonstanton, la grandoeksponenton kaj la akcepteblecon de la tuta cirkvitfamilio. Se akceptebla familio ne ekzistas, la valoro estas senfina. Punkta infimumo povas elekti malsamajn familiojn je malsamaj tempoj. `RealizesProfile` esprimas asimptotan algoritman rezulton per unu familio, kiu realigas la tutan profundoprofilon.
- La kunmeta `BinaryCircuit.depth` estas strukture pruvita supra baro. Kongruo de la supra kaj malsupra baroj certigas optimumon.
- A, B kaj C estas sufiĉaj kriterioj. Lean kontrolas la konstruojn kaj semantikajn pruvojn donitajn de la uzanto. Aŭtomata serĉo de atestiloj por ĝeneralaj reguloj bezonus propran algoritmon.
- B postulas kompletan simulan atestilon por la konkreta sistemo. P-kompleteco ankaŭ postulas, ke la cellingvo apartenu al P. La apartiga supozo implicas nemembrecon en unuforma NC.
- En luma konuso de polinoma grando C donas maksimume logaritman malsupran baron per nombrado. La malsupra baro por fiksita regado mezuras la profundon de cirkvitoj kun po maksimume du eniroj en ĉiu pordego. Pruvo de NC¹-kompleteco postulus NC¹-malfacilecon sub taŭga redukto.

La kontrolitaj klasifiko kaj drataro precizigas, kiam la prognozilo por fiksita regado estas reuzebla. La ekzemplo kun adicia regado donas alian resumon de la koeficientoj, kiun oni povas kunmeti. Sekva demando estas, kiuj ordosentemaj resumoj restas uzeblaj kun la sama rega evoluo kaj alia saltogardo.

La aksiomkontrolo sekvas transitivajn dependecojn de projektaj teoremoj ĝis la eksteraj kompleksecaj fundamentoj. La difinoj, teoremaj deklaroj kaj kontrolgvidilo ebligas kontroli la modelojn kaj supozojn. [Fidlimoj](docs/dependencies.md)
