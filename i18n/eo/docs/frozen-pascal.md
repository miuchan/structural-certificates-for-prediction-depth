# Unuflanka ĉela aŭtomato kun fiksita regado

[English](../../../docs/frozen-pascal.md) · [简体中文](../../zh-CN/docs/frozen-pascal.md) · [日本語](../../ja/docs/frozen-pascal.md) · **Esperanto**

## Modelo kaj eniro

Fiksu la larĝon $`q`$ de regvorto kaj du buleajn funkciojn $`s,h:\{0,1\}^q\to\{0,1\}`$. Ĉiu kradpunkto $`i\in\mathbb Z`$ havas regvorton $`a_i`$ kaj datuman biton $`x_i\in\mathbb F_2`$. La sinkrona ĝisdatigo estas

```math
a_i'=a_i,\qquad x_i'=s(a_i)x_i+h(a_i)x_{i+1}.
```

La regvortoj estas parto de la komenca agordo kaj elekteblas sendepende por ĉiu ĉelo. Por donita regagordo, la datuma trako evoluas per lineara mapo. La kuna regulo povas esti neafina. Ekzemple, kun $`s=\mathrm{AND}`$ kaj $`h=\mathrm{OR}`$, eĉ sub la limigo $`x_{i+1}=0`$ la koeficiento de $`x_i`$ dependas de $`a_i`$, dum ĉe afina funkcio tiu koeficiento devas esti fiksa. La regvortoj restas senŝanĝaj dum la datumaj bitoj povas varii laŭ tempo.

Demando pri tempo $`T`$ eksplicite donas la komencajn valorojn ĉe $`0,\ldots,T`$. La kodo listigas la $`T+1`$ regvortojn, poste la respondajn datumajn bitojn. Valida longo de la norma prognoza lingvo estas $`n=(q+1)(T+1)`$. La longo do determinas $`T=n/(q+1)-1`$, kaj la demando estas akceptata ĝuste kiam $`x_0(T)=1`$. La lingvo malakceptas la malplenan ĉenon kaj longojn, kiuj ne kodas tutajn ĉelojn. Ĉar $`q`$ estas fiksa, logaritma profundo estas logaritma kaj laŭ $`T+2`$ kaj laŭ la tuta enirlongo. Mallonga priskribo de la komenca stato kun aparta duuma tempo bezonas propran enirmodelon. [Fenestrosemantiko](../../../PredictionDepth/FrozenPascal/Window.lean) · [Enirkodado](../../../PredictionDepth/FrozenPascal/GuardRules.lean) · [Prognoza lingvo](../../../PredictionDepth/FrozenPascal/UniformLanguage.lean)

## Klasifika teoremo

Fiksu $`q`$ kaj la cirkvitojn de De Morgan por $`s,h`$ kun profundoj $`d_s,d_h`$. La cirkvitoj povas havi arbitran drataron kaj komunajn mezajn rezultojn. Estu $`p=\operatorname{popcount}(T)`$ la nombro de unubitoj de $`T`$ kaj $`\ell(v)=\lceil\log_2 v\rceil`$. Por ĉiu valida tempo, ĉiu ĝusta bulea cirkvito kun enira grado maksimume du plenumas la malsupran baron en la tabelo. Unu sama logspac-unuforma familio de cirkvitoj de De Morgan kun polinoma nombro da pordegoj realigas la suprajn barojn. La familio decidas la tutan lingvon kaj malakceptas ĉiujn nevalidajn longojn. [Unuforma klasifika teoremo](../../../PredictionDepth/FrozenPascal/UniformClassification.lean)

| Semantika kondiĉo de la fiksa regulo | Malsupra profundobaro | Supra profundobaro de la unuforma familio |
| --- | --- | --- |
| $`h\equiv 0`$ | $`0`$ | $`1+d_s`$ |
| $`h\equiv 1,\ s\equiv 0`$ | $`0`$ | $`0`$ |
| $`h`$ nekonstanta, aŭ $`h\equiv 1`$ kun $`s`$ nekonstanta | $`\ell(T+1)`$ | $`104(\ell(T+3)+1)+\max(d_s,d_h)`$ |
| $`h\equiv 1,\ s\equiv 1`$ | $`p`$ | $`3p`$ |

Do ĉiuj fiksitaj reguloj havas prognozajn lingvojn en logspac-unuforma NC¹, kaj ĝuste la unuaj du klasoj apartenas al unuforma NC⁰. La tria klaso havas logaritman profundon ĉe ĉiu pozitiva tempo. La kvara havas maksimume tri tavolojn je tempo $`2^r`$ kaj almenaŭ $`r`$ tavolojn je $`2^r-1`$. Sekve mankas komuna konstanta profundobaro por ĉiuj tempoj. Je $`T=0`$ la minimuma profundo ĉiam estas nula, ĉar la eliro estas la enira drato $`x_0(0)`$. [Unuforma NC¹](../../../PredictionDepth/FrozenPascal/UniformLanguage.lean) · [Necesa kaj sufiĉa kondiĉo por unuforma NC⁰](../../../PredictionDepth/FrozenPascal/UniformClassification.lean)

## Koeficienta formulo

Disvolvu $`x_0(T)`$ kiel linearan kombinon de la komencaj datumaj bitoj. Estu $`s_k=\sum_{i=0}^{k}s(a_i)`$ entjera nombro kaj $`e_k=\prod_{i=0}^{k-1}h(a_i)`$ la indikilo, ke la unuaj $`k`$ eĝoj estas traireblaj. La malplena produto estas $`1`$. Tiam

```math
x_0(T)=\sum_{k=0}^T e_k\,\operatorname{multichoose}(s_k,T-k)\,x_k(0)
\qquad\text{en }\mathbb F_2.
```

Ĉiu kontribuanta vojo de kradpunkto $`k`$ ĝis la origino moviĝas maldekstren ekzakte $`k`$ fojojn kaj transiras la samajn eĝojn laŭvice. Tio donas la komunan faktoron $`e_k`$. La ceteraj $`r=T-k`$ paŝoj estas distribuitaj inter ĉeloj, kiuj permesas restadon, inkluzive de la komenca kaj fina ĉeloj. La vizitordo estas fiksa, do ĉiu atribuo de restopaŝoj determinas unu vojon. Por $`s_k>0`$ ekzistas $`\binom{s_k+r-1}{r}`$ vojoj. Por $`s_k=0`$ ekzistas unu vojo se $`r=0`$ kaj alie neniu. La koeficiento estas tiu nombro module $`2`$. `iterate_data` pruvas per koeficienta rikuro, ke la formulo kongruas kun la efektiva iteracio sur senfina krado. [Koeficienta rikuro kaj `iterate_data`](../../../PredictionDepth/FrozenPascal/Semantics.lean)

Ekzemple, estu $`T=3`$, la restindikiloj $`(1,0,1,0)`$ kaj la unuaj tri eĝoj traireblaj. La kontribuo de ĉelo $`2`$ bezonas unu restopaŝon, kiu povas okazi ĉe ĉelo $`0`$ aŭ $`2`$. La du vojoj nuligas unu la alian en $`\mathbb F_2`$, do $`x_0(3)=x_0(0)\oplus x_1(0)\oplus x_3(0)`$.

## Paralela algoritmo

Por donita longo, la tempo $`T`$ jam estas konata dum generado de la cirkvito. La cirkvito unue taksas ambaŭ gardojn paralele en ĉiuj ĉeloj, kaj poste paralele kalkulas la jenon por ĉiu $`0\le k\le T`$.

1. Kalkulu $`e_k`$ per ekvilibra AND-arbo. Nombru la $`k+1`$ restindikilojn per adiciarbo kun konservataj retenoj (*carry-save*). Ĉiu rondo grupigas duumajn nombrojn kaj paralele kunpremas ĉiun grupon de tri vicoj al du per konstanta profundo. Post $`O(\log(T+2))`$ rondoj restas du vicoj. La fina propagado de retenoj bezonas profundon $`O(\log(T+2))`$ eĉ per adiciilo lineara laŭ la bitlarĝo.
2. Elektu $`\operatorname{multichoose}(s_k,T-k)\bmod 2`$ laŭ la nombro $`s_k`$. Por ĉiu ebla nombro $`v=0,\ldots,k+1`$ la generilo anticipe kalkulas la koeficientan biton. Dum rulado la cirkvito paralele komparas $`s_k=v`$ kaj reduktas la kongruajn erojn per ekvilibra arbo. Por $`v>0`$ la teoremo de Lucas esprimas la koeficientan biton per duuma implico. Ĉiu unubito de $`T-k`$ ankaŭ devas esti unubito de $`v+T-k-1`$. Por $`v=0`$ la bito estas determinita de $`T=k`$.
3. Multipliku la koeficientan biton per $`e_k`$ kaj $`x_k(0)`$, kaj kombinu ĉiujn termojn per ekvilibra XOR-arbo. En la pordegobazo de De Morgan, malgranda cirkvito de fiksa profundo realigas ĉiun du-eniran XOR.

Ĉiu stadio uzas profundon $`O(\log(T+2))`$. Eĉ apartaj subcirkvitoj por ĉiuj prefiksoj bezonas nur polinoman nombron da pordegoj. La ŝlosila redukto esprimas spactempajn transirkoeficientojn per prefiksaj nombroj, traireblaj eĝoj kaj pareco de kombinatorikaj nombroj. [Nombrada cirkvito](../../../PredictionDepth/FrozenPascal/UniformWeight.lean) · [Bittesto de Lucas](../../../PredictionDepth/FrozenPascal/CoefficientBits.lean) · [Elekto kaj redukto de koeficientoj](../../../PredictionDepth/FrozenPascal/UniformDecoder.lean)

## Lean-konstruo kaj logspaca unuformeco

La supra algoritmo povas esti rekte organizita por fiksita tempo. La Lean-konstruo ligas la saman malkodadon al ĝenerala voja kompililo por reuzi la kunmetan interfacon kun rimedobaroj. La abstrakta prezento interpretas tempon $`u`$ kiel la $`u`$-an iteracion. Kunmeto adicias du tempojn. La cirkvito konservas gardindikilojn, datumajn bitojn kaj unu-aktivan tempetikedon (*one-hot*) ene de la fenestro. Pravalorizo metas la etikedon ĉe pozicio $`0`$, kvadratigo duobligas la pozicion, kaj multipliko per la semo pligrandigas ĝin je unu. La malkodilo uzas la etikedon por elekti la bezonatan koeficientvicon. La tempoprezento kaj la drataro de la vojo faras kunmeton kaj vicelekton. La rapida prognozo venas el la koeficienta formulo en la malkodilo. `no_global_decoder` karakterizas la fenestrolimon de la etikedokodo. Por fenestro kun almenaŭ du ĉeloj, ekzistas unu fiksita komenca agordo por kiu du tempoj ekster la fenestro donas malsamajn respondojn malgraŭ du tute nulaj etikedoj. [Voja atestilo](../../../PredictionDepth/FrozenPascal/PathWitness.lean) · [Apartigo ekster la fenestro](../../../PredictionDepth/FrozenPascal/Separation.lean)

La aparta konstruo `guardedPrediction` por ĉiu tempo havas eksplicitajn rimedobarojn. Se $`g_s,g_h`$ estas la pordegonombroj de la du gardaj cirkvitoj, ĝiaj profundo kaj pordegonombro estas maksimume, respektive,

```math
7+33\lceil\log_2(T+2)\rceil+\max(d_s,d_h),\qquad
113(T+2)^4+(T+1)(g_s+g_h).
```

Alia konstruo `uniformGuardedPrediction` havas apartan logspacan generilon. Kun `UniformWeight.basis` la profundobaro ĉe valida tempo estas

```math
104\bigl(\lceil\log_2(T+3)\rceil+1\bigr)+\max(d_s,d_h).
```

Sur nurlegebla unuma eniro $`1^n`$, la generilo determinas validecon kaj $`T`$. Per indicoj de logaritma bitlarĝo ĝi generas la nombradajn tavolojn, la koeficientajn termojn, la reduktan arbon kaj la etikedodrataron. La konkreta nombrada cirkvito kunpremas la kvar vicojn de ĉiu paro da arbaj nodoj al du vicoj por unuforme aranĝi la drataron. Trarigardo de duumaj bitoj generas la parecon de la kombinatorikaj nombroj. La laborbendo bezonas nur mallongajn indicojn kaj lokan komputstaton. La formala pruvo kunmetas la seriigilojn de la blokoj en unu haltantan multbendan transduktilon. Ĝi eligas la kompletan cirkvitkodon, inkluzive de tipoj de pordegoj, numeroj de antaŭuloj kaj elirnumeroj. La polinoma grando sekvas el la baro por la elirlongo de la maŝino. `predictionLanguage_mem_uniformNC_one` kunigas ĝustecon, profundon, grandon kaj la generilon en unu sama cirkvitfamilio. [Rimedobaroj por ĉiu tempo](../../../PredictionDepth/FrozenPascal/GuardRules.lean) · [Generilo kaj profundobaro](../../../PredictionDepth/FrozenPascal/UniformPrediction.lean) · [Spacpruvo por koeficientaj bitoj](../../../PredictionDepth/FrozenPascal/CoefficientUniform.lean) · [Difino de unuforma NC](../../../PredictionDepth/Complexity/UniformNC.lean)

## Kongrua malsupra profundobaro

Supozu, ke ekzistas regvortoj $`a_{\rm on},a_{\rm off}`$ tiaj, ke

```math
(s(a_{\rm on}),h(a_{\rm on}))=(1,1),\qquad
(s(a_{\rm off}),h(a_{\rm off}))=(0,1).
```

Metu $`a_{\rm on}`$ ĉe la origino kaj $`a_{\rm off}`$ en la ceteraj ĉeloj. Tiam $`e_k=1`$ kaj $`s_k=1`$ por ĉiu $`k`$, kaj la prognozo estas la pareco de la $`T+1`$ datumaj bitoj. Kun tiuj fiksitaj regvortoj, inversigo de iu sola datuma bito inversigas la rezulton. Do la origina prognoza funkcio havas almenaŭ $`T+1`$ esencajn enirojn. La malantaŭa konuso de cirkvito kun du eniroj po pordego kaj profundo $`d`$ atingas maksimume $`2^d`$ enirojn, eĉ kun komunaj subcirkvitoj kaj arbitraj longdistancaj dratoj. Tial

```math
d\ge \lceil\log_2(T+1)\rceil.
```

Por la gardoj AND kaj OR elektu $`a_{\rm on}=(1,1)`$ kaj $`a_{\rm off}=(1,0)`$. Kun la supra baro tio donas asimptote optimuman profundon $`\Theta(\log(T+2))`$ por du-eniraj pordegoj. [Ĝenerala malsupra baro kaj ekzemplo kun AND kaj OR](../../../PredictionDepth/FrozenPascal/LowerBound.lean)

## Pruvo de ĉiu branĉo

`classify` kontrolas regvortojn laŭ prefiksoj kaj ĉesigas la nunan provon pri konstanteco ĉe la unua kontraŭekzemplo. Elĉerpa provo ankoraŭ povas viziti $`2^q`$ regvortojn. `classify_eq_iff` kontrolas la ekvivalentecon inter la rezulto kaj la responda semantika kondiĉo, kaj `guard_depth_cases` kontrolas, ke la kvar kazoj kovras ĉiujn fiksitajn gardajn funkciojn. Ekzemple, kun fiksa $`s\equiv1`$, decidi konstantan profundon ekvivalentas al decidi ĉu la cirkvito $`h`$ estas nekontentigebla. [Klasifikilo kaj necesa kaj sufiĉa kondiĉo por limigita profundo](../../../PredictionDepth/FrozenPascal/Classification.lean)

Se $`h\equiv0`$, la eliro ĉe pozitiva tempo estas $`s(a_0)x_0(0)`$. Ĝia realigo postulas la restogardan cirkviton kaj unu AND-pordegon. Se $`h\equiv1,s\equiv0`$, sufiĉas la drato $`x_T(0)`$. Kaj la profundo kaj la pordegonombro estas nulaj. [Du konstantprofundaj konstruoj](../../../PredictionDepth/FrozenPascal/Classification.lean)

Se $`h`$ estas nekonstanta, fiksu la datumajn bitojn tiel ke nur $`x_T(0)=1`$. La eliro estas $`e_T`$, ĉar la plej fora eniro povas atingi la originon nur per vojo konsistanta tute el saltoj. Ĉiu paro de regvortoj en la bulea hiperkubo estas ligita per vojo, kiu inversigas po unu biton. Do nekonstanta $`h`$ ŝanĝas sian valoron ĉe iu eĝo. En ĉiu el la unuaj $`T`$ ĉeloj uzu tian eĝon kaj fiksu la ceterajn ĉelojn por permesi la transiron. Tio montras, ke ĉiu el tiuj ĉeloj havas almenaŭ unu esencan regbiton. Permesante ĉiujn transirojn, oni vidas ankaŭ, ke $`x_T(0)`$ estas esenca. Do la profundo estas almenaŭ $`\lceil\log_2(T+1)\rceil`$. Se $`h\equiv 1`$ kaj $`s`$ estas nekonstanta, la pareca limigo en la antaŭa sekcio donas la saman baron. [Komuna malsupra baro por ambaŭ variaj kazoj](../../../PredictionDepth/FrozenPascal/Classification.lean)

La enira grado determinas la amplekson de tiu baro. Ekzemple, se $`s\equiv0, h(a)=a`$, la prognozo estas $`x_T(0)\land a_0\land\cdots\land a_{T-1}`$. Du-eniraj pordegoj bezonas logaritman profundon, dum unu AND-pordego kun nelimigita enira grado sufiĉas.

Se ambaŭ funkcioj estas konstante $`1`$, la prognozo estas la pareco de la datumaj bitoj ĉe la neparaj koeficientoj de la Pascal-vico. Estu $`p=\operatorname{popcount}(T)`$. La indicoj de la neparaj koeficientoj estas la duumaj submaskoj de $`T`$, do $`2^p`$ datumaj bitoj estas esencaj. Lean kontrolas la minimuman profundon $`p`$ kun denaska du-enira XOR, kaj la minimuman De Morgan-profundon nul por $`p=0`$ kaj $`2p+1`$ por $`p>0`$, kiam NOT kalkuliĝas kiel unu tavolo. De $`T=2^r-1`$ al $`T=2^r`$ la minimuma De Morgan-profundo falas de $`2r+1`$ al tri tavoloj por $`r\ge2`$. La preciza minimumo je ĉiu tempo kaj la unuforma supra baro $`3p`$ de la sekva sekcio uzas apartajn konstruojn. [Subteno kaj teoremo por denaska XOR](../../../PredictionDepth/FrozenPascal/HomogeneousPascal.lean) · [Teoremo pri minimuma De Morgan-profundo](../../../PredictionDepth/FrozenPascal/PascalExactDepth.lean)

## Realigo de la unuforma familio

`classifiedPrediction` elektas generilon laŭ la klasifiko de la fiksa regulo. La regulo estas fiksa en la difino de la cirkvitfamilio, kaj la generilo varias laŭ la enirlongo. La generiloj por konstante malpermesita salto kaj por pura ŝovo eligas kompletajn kodojn de la specialaj cirkvitoj, konservante respektive la konstantan profundobaron kaj la nulan pordegonombron. Variaj gardoj reuzas la ĝeneralan vojan cirkviton. La homogena Pascal-generilo trairas $`k\le T`$ kaj uzas submaskan teston por flue eligi dratojn de neparaj koeficientoj. La redukta cirkvito traktas nur tiujn enirojn. [Generiloj por malpermesita salto kaj ŝovo](../../../PredictionDepth/FrozenPascal/UniformLocal.lean) · [Pascal-generilo](../../../PredictionDepth/FrozenPascal/UniformHomogeneous.lean)

La Pascal-redukto uzas $`p`$ rondojn de paralelaj XOR-pordegoj de fiksa larĝo, kun tri tavoloj de De Morgan-pordegoj en ĉiu rondo. Tio ebligas rekte kunigi la elirojn de la rondoj flue, donante profundon maksimume $`3p`$ kaj $`5p2^p`$ pordegojn. Ĉar $`2^p\le T+1`$, la nombro de pordegoj kreskas maksimume laŭ $`T\log(T+2)`$. La antaŭa ekvilibra arbo por ĉiu tempo havas malpli da pordegoj, kaj la unuforma teoremo uzas la konstruon de fiksa larĝo. [XOR-redukto kaj kodado](../../../PredictionDepth/FrozenPascal/UniformXor.lean)

## Du komparoj kun evoluanta regado

Kun unuforme ŝoviĝanta rega trako oni povas konservi ambaŭ branĉojn por restado kaj salto. Lean kontrolas, ke speguli la koordinatojn laŭ la moviĝo fiksas la regadon kaj interŝanĝas la du gardojn. Rekonekti la enirojn de la finia fenestro ebligas reuzi la prognozan cirkviton por fiksita regado kun la sama nombro da pordegoj kaj sen pligrandigo de la profundo. [Moviĝanta referenca kadro kaj fenestra drataro](../../../PredictionDepth/TransportedBranching.lean)

Por $`c'_i=c_i\oplus c_{i+1}`$ kaj $`x'_i=c_ix_i\oplus x_{i+1}`$, la prefiksaj nombroj de la fiksa modelo ne determinas la koeficientojn. La koeficiento de datumbito $`T`$ estas 1. Por $`k<T`$ ĝi estas la komuna Pascal-pareco $`Q_T=c_0(T)\oplus c_T(0)`$ multiplikita per la indikilo, ke la rega sufikso $`c_{k+1}(0),\ldots,c_{T-1}(0)`$ estas tutnula. Lean kontrolas la koeficientan formulon. En la artikolo, ekvilibra redukto donas linearan pordegonombron kaj logaritman profundon, kun kongrua logaritma malsupra baro. [Lean-formulo](../../../PredictionDepth/AdditiveBranching.lean) · [Pruvo de la cirkvitaj baroj](../../../paper/structural-certificates.eo.pdf)

## Amplekso kaj indekso de formaligo

Por eksplicita eniro de $`n`$ bitoj, malsupra baro el la nombro de esencaj eniroj estas maksimume $`\ell(n)`$. Eĉ luma konuso de polinoma volumeno en fiksa dimensio tiel donas maksimume logaritman malsupran baron laŭ $`T`$. La supra baro ĉi tie validas por unuflankaj reguloj kun fiksita regado kaj unuĉela eliro. La prognoza lingvo ricevas la tutan komencan fenestron, kaj la generilo ricevas la enirlongon en unuma kodo. La norma kadro por P-malfacileco uzas apartan demandokodadon kun unuma tempokampo. Ĝia uzanto devas provizi konkretan simulon kaj logspacan redukton, kiu generas la tutan demandon. [Limo de nombrado de dependecoj](../../../PredictionDepth/DependencyGrowth.lean) · [Devoj en la kadro por malfacileco](hardness.md)

| Kontrolata rezulto | Lean-deklaro |
| --- | --- |
| Sinkrona ĝisdatigo sur senfina krado kaj koeficienta formulo | [`iterate_data`](../../../PredictionDepth/FrozenPascal/Semantics.lean) |
| Malsupra profundobaro ĉe ĉiu tempo por arbitra ĝusta prognozilo kun du eniroj po pordego | [`classifiedPrediction_depth_lower_bound`](../../../PredictionDepth/FrozenPascal/UniformClassification.lean) |
| Necesa kaj sufiĉa kondiĉo por komuna konstanta profundobaro je ĉiuj tempoj | [`bounded_prediction_depth_iff`](../../../PredictionDepth/FrozenPascal/Classification.lean) |
| Kardinalo de la Pascal-subteno kaj rimedobaroj de la ekvilibra arbo por ĉiu tempo | [`pascalSupport_card`, `homogeneousPrediction_depth`, `homogeneousPrediction_size`](../../../PredictionDepth/FrozenPascal/HomogeneousPascal.lean) |
| Minimuma profundo de la homogena Pascal-regulo je ĉiu tempo | [`homogeneousNativeXorPrediction_depth`](../../../PredictionDepth/FrozenPascal/HomogeneousPascal.lean) · [`homogeneous_prediction_deMorgan_exact_depth`](../../../PredictionDepth/FrozenPascal/PascalExactDepth.lean) |
| Lingva ĝusteco, logspaca unuformeco kaj branĉaj baroj por la sama familio | [`uniform_depth_classification`](../../../PredictionDepth/FrozenPascal/UniformClassification.lean) |
| Necesa kaj sufiĉa kondiĉo por unuforma NC⁰ je ĉiuj enirlongoj | [`predictionLanguage_mem_uniformNC_zero_iff`](../../../PredictionDepth/FrozenPascal/UniformClassification.lean) |

## Komparo kun la literaturo

En sia artikolo en *Physica D*, Moore dividas tempintervalojn por trovi transirkoeficientojn de neaŭtonomaj adiciaj ĉelaj aŭtomatoj. La koeficientoj povas varii samtempe laŭ tempo kaj pozicio. Lemo 1 en §3 de la antaŭpresaĵo donas cirkvitojn ACC¹ kun modulaj adiciaj pordegoj de nelimigita enira grado. Per du-eniraj pordegoj la metodo realigas profundon $`O(\log^2 T)`$. Teoremo 1 traktas kvazaŭ-rektan produton en kiu alia trako regas tiujn koeficientojn. Por space homogenaj adiciaj reguloj la artikolo jam generas Pascal-vicon en logaritma spaco kaj akiras unuforman ACC⁰ per modulaj adiciaj pordegoj de nelimigita enira grado. Glaisher jam kalkulis la neparajn koeficientojn, kaj Rowland klarigas la rilaton al la teoremo de Lucas. [Artikolo en la revuo](https://doi.org/10.1016/S0167-2789(97)80003-6) · [Antaŭpresaĵo §3](https://arxiv.org/pdf/patt-sol/9701008) · [Rowland §1](https://arxiv.org/pdf/1001.1783)

Kun fiksitaj regvortoj la datuma evoluo estas lineara operatoro kun supra dudiagonala matrico. La diagonalaj elementoj estas $`s(a_i)`$, kaj tiuj sur la superdiagonalo estas $`h(a_i)`$. Teoremo 6.1 de Higham esprimas la elementojn de funkcio de supra dudiagonala matrico super la kompleksaj nombroj per produto kaj dividita diferenco. Por potencfunkcio la dividita diferenco estas kompleta homogena simetria polinomo. Se la diagonalaj variabloj estas $`0`$ aŭ $`1`$, la polinomo nombras monomojn de tuta grado $`T-k`$ kun subteno en la ĉeloj, kiuj permesas restadon, donante la saman multielektan koeficienton. Ĉi tie vojnombrado rekte pruvas la specialigon en $`\mathbb F_2`$ kaj ebligas analizi paralelajn rimedojn kaj kontroli la unuforman konstruon. [Higham, teoremo 6.1](https://doi.org/10.13001/ela.2024.8297)

La projekto ligas la unuflankan specialigon kun space arbitra kaj tempe fiksa regado al maŝinnivela supra baro en unuforma NC¹ kaj kvarbranĉa profundoklasifiko. La supra baro $`O(\log T)`$ por fiksita regado estas komparebla al la garantio de la divida metodo de Moore por pli ĝeneralaj koeficientoj. La konsultita literaturo ankoraŭ ne determinas prioritaton de la unuforma supra baro kaj la kompleta klasifiko por tiu preciza regulfamilio.
