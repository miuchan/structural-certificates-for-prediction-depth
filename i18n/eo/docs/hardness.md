# Teoremo B. Simula redukto kaj kondiĉa malfacileco

[English](../../../docs/hardness.md) · [简体中文](../../zh-CN/docs/hardness.md) · [日本語](../../ja/docs/hardness.md) · **Esperanto**

La norma komplekseca tavolo troviĝas en `PredictionDepth/Complexity/Logspace.lean`, `CVP.lean` kaj `StandardHardness.lean`, en la nomspaco `PredictionDepth.StandardComplexity`. `PredictionDepth/Hardness.lean` konservas la ĝeneralajn helpajn teoremojn kaj la unuman demandokodadon.

## Norma komplekseca tavolo

`StandardComplexity.Logspace` uzas la multbendajn Turing-maŝinojn de cslib kun finia regado kaj duuma alfabeto. La enira bendo estas nurlegebla, la elira bendo estas nuraldonebla, kaj la laborspaco estas mezurata per la nombro de vizititaj laborbendaj ĉeloj. `logspace_comp` aplikas la pruvitan rekomputan kompililon. Kiam la dua maŝino bezonas simbolon de la meza rezulto, ĝi rerulas la unuan maŝinon sen konservi la tutan mezan ĉenon.

`CVP.lean` uzas konkretajn cirkvitojn de De Morgan, enirajn valorasignojn kaj injektivan duuman kodadon. La importita `cvp_logSpaceComplete` jam pruvas P-kompletecon de CVP per komputtabelaj cirkvitoj por polinomtempaj maŝinoj kaj logspaca seriigilo. Tiu tavolo do jam provizas la malfacilecon de la fontoproblemo kaj fermitecon sub reduktoj.

`StandardComplexity.SimulationWitness` postulas la jenajn simulajn datumojn por konkreta dinamika sistemo.

1. Mapo de ĉiu valida CVP-instanco al simula tempo kaj kodo de la komenca stato.
2. Pruvo per logspaca maŝino, kiu generas **la tutan demandon kun unuma tempo**.
3. Pruvo, ke la observado de la dinamika sistemo je tiu tempo egalas la eliron de la origina cirkvito.

`SimulationWitness.prediction_P_hard` deduktas `LogSpaceHard @Cslib.Complexity.P` por la efektiva P-klaso. Maŝinpruvo, ke la cela prognoza lingvo apartenas al tiu P, aldone donas `prediction_P_complete`. `time_polynomial` kaj `payload_length_polynomial` derivas polinomajn barojn por la tempokampo kaj la kodolongo el la logspaca demandogenerilo.

Kvankam CVP uzas tipon de validaj instancoj, la rezulto pri la celo estas ordinara lingva malfacileco. La malfacileca teoremo de CVP ampleksas ĉiujn enirkodadojn, aparte ĉiujn duumajn vortojn kun `encBits`. La redukto ĉiam eligas validan instancon. La cela prognoza lingvo estas difinita sur ĉiuj duumaj vortoj kaj malakceptas ĉiun nevalidan demandon.

La norma maŝinfundamento devenas de la fiksita enmeto [cslib-frontier `3c44ce0b`](https://github.com/cslib-community/cslib-frontier/tree/3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d). Lean kompilas la dependecan fontkodon kaj la projektan kodon. La literaturo servas kiel matematika kunteksto. La koncernaj moduloj pri paralela komplekseco ligas la kompletan tavolon pri unuforma NC kaj ties kondiĉajn konkludojn.

## Ĝenerala helpa tavolo

La parametrohavaj teoremoj de `PredictionDepth.Hardness` ebligas reuzon kun aliaj klasoj de reduktoj.

1. `encodeQuery t x = 1^t 0 x` estas duuma demando kun unuma tempokodo. `decode_encodeQuery` kaj `encode_decodeQuery` pruvas, ke kodado kaj malkodado estas inversaj, kaj `encodeQuery_injective` pruvas malambiguecon. `decoded_time_le_length` garantias, ke la tempo en valida demando estas maksimume ĝia longo. Nevalidaj demandoj estas malakceptataj.
2. `predictionProblem F observe decodeState` kalkulas `observe ((F^[t]) (decodeState x))` por valida demando. La kodo de la enira stato kaj la stattipo de la dinamika sistemo estas apartaj.
3. `SimulationWitness` enhavas la enirkodon, la simulan tempon, iliajn polinomajn barojn kaj pruvon, ke por ĉiuj eniroj la simula eliro egalas la respondon de la fontoproblemo. `query_length_polynomial` derivas polinoman longobaron por la tuta unuma demando el la tempo kaj la kodolongo.
4. Donita pruvo de akceptebleco de la plena demandogenerilo, `SimulationWitness.reduction` konstruas plur-al-unu-redukton. La simula semantiko establas la ĝustecon de la redukto.
5. `Reduction.trans` kunmetas reduktojn. `prediction_P_hard` transigas P-malfacilecon de la fonto al la prognoza problemo. Pruvo, ke la prognoza problemo apartenas al P, aldone donas `prediction_P_complete`.
6. `prediction_not_NC` pruvas, ke la prognoza problemo estas ekster la elektita paralela klaso, se tiu klaso estas subaro de P, fermita sub la elektitaj reduktoj kaj malsama ol P. La konkludo koncernas klasmembrecon.

## Difinoj kaj eksplicitaj supozoj

`InP` uzas `Turing.TM2ComputableInPolyTime` de Mathlib. La enirkodo estas la duuma vorto mem, la eliro estas bulea bito kaj ĉiu stako devas havi finian alfabeton. Tiu aldona postulo necesas ĉar en `FinTM2` de Mathlib la strukturo garantias finiecon nur por la alfabeto de la enira stako. `FinTM2` provizas finiajn etikedojn, finiajn regstatojn kaj finian nombron da stakoj. La pruvo evitas dependecon de la ankoraŭ nepruvita `TM2ComputableInPolyTime.comp` de Mathlib.

`TM2.Stmt` kaj `stepAux` montras, ke la funkcioj de ĉiu instrukcio aliras nur finian regstaton kaj maksimume unu simbolon ĉe la supro de stako. Ĉiu etikedo havas finian instrukcian sintakson, kaj la nombro de etikedoj estas finia. Tial mezuro laŭ `step` enkalkulas ĉiun paŝon de nelimigita komputado. `stack_InP_implies_standard_P` en `Complexity/StackMachineBridge.lean` uzas pruvitan simulon de TM2 per multbenda maŝino por transporti la helpan maŝinatestilon al la norma klaso P.

La jenaj kvar parametroj apartenas al la parametrohavaj teoremoj de la helpa tavolo. La norma tavolo jam solvas la devojn pri CVP-malfacileco kaj klasa fermiteco.

| Parametro de la helpa tavolo | Celata norma instanco | Traktado en la norma tavolo |
| --- | --- | --- |
| `ReductionSystem.Admissible` kun fermiteco sub idento kaj kunmeto | Logspaca transdukto de totalaj funkcioj | `Complexity/Logspace.lean` uzas efektivajn maŝinojn kaj pruvitan fermitecon sub kunmeto. |
| `hencode` | La tuta demando, inkluzive de la unuma tempoĉeno, estas generebla en logaritma spaco. | La konkreta simula konstruo devas ĝin provizi. |
| `hsource : PHard S source` | CVP kun la elektita kodado estas P-malfacila. | `Complexity/CVP.lean` uzas pruvitan komputtabelan redukton el konkretaj Turing-maŝinoj. |
| `ParallelClassAssumptions S NC` | Logspac-unuforma NC estas subaro de P kaj estas fermita sub la elektitaj reduktoj. | `UniformNC`, `UniformReachability` kaj `NCClosure` provizas la efektivajn difinojn kaj pruvojn. |

`prediction_P_complete` eksplicite postulas ankaŭ `hP`, maŝinpruvon pri la cela prognoza lingvo per polinomtempa Turing-maŝino kun finia alfabeto. Por ĉelaj aŭtomatoj kun fiksa finia najbaraĵo kaj unuma tempo, tipa pruvo simulas la paŝojn unu post alia. La modulo lasas al la uzanto konstrui la maŝinon por la elektita loka regulo.

La redukto bezonas polinoman longobaron por la elira demando. La spaca baro por la tuta prognozita trajektorio venas de la analizo de la konkreta simulo. `payload_polynomial` pruvas longobaron por la kodo de la komenca stato. Lokeco, pordegaj konstrublokoj, kanaloj, sinkronigo kaj kruciĝoj estas metodoj por pruvi `simulation_correct` kaj `hencode`. Por transigi malfacilecon sufiĉas plenumi la rezultajn semantikajn kaj reduktajn devojn.

La supozoj de la helpa interfaco apartenas al la ĝenerala tavolo. Por la normaj konkludoj pri P-malfacileco kaj P-kompleteco uzu `StandardComplexity.SimulationWitness`, kiu jam enkorpigas efektivajn logspacajn maŝinojn kaj pruvitan CVP-kompletecon. La Lean-tipoj montras ĉiujn devojn de la konkreta sistemo. Oni povas ilin inspekti per `#check`.

## Referencoj

La logspaca P-kompleteco de CVP devenas de Richard E. Ladner, *The Circuit Value Problem is Log Space Complete for P*, SIGACT News 7(1), 18–20, 1975. [Bibliografio de la aŭtoro](https://homes.cs.washington.edu/~ladner/papers.html)

Pri P-kompleteco, NC-reduktoj, transigo de malfacileco kaj la rilato al disiĝo de P kaj NC, vidu *Limits to Parallel Computation: P-Completeness Theory* de Greenlaw, Hoover kaj Ruzzo, precipe la ĉapitrojn pri reduktoj kaj CVP. La literaturo prezentas la matematikan kuntekston, kaj la maŝina kontrolo uzas pruvterminojn el la dependecaj bibliotekoj kaj ĉi tiu deponejo. [Plena libro disponigita de la aŭtoroj](https://homes.cs.washington.edu/~ruzzo/papers/limits.pdf)
