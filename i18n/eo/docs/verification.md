# Kontrolregistro

[English](../../../docs/verification.md) · [简体中文](../../zh-CN/docs/verification.md) · [日本語](../../ja/docs/verification.md) · **Esperanto**

La projekto fiksas Lean al `v4.36.0-rc2` kaj fiksas la [versiojn de la dependecoj](dependencies.md). Rulu la jenan komandon el la deponeja radiko.

```sh
./scripts/check.sh
```

La skripto kontrolas la modulan kovradon de la defaŭlta enirejo, rulas `lake build --wfail`, kontrolas la transitivajn aksiomajn dependecojn de la projektaj deklaroj kaj rulas negativan regresian teston.

## Nuna loka kontrolo

La nuna macOS-kontrolo kovris la minimumajn profundojn de la homogena Pascal-regulo kaj la du novajn modulojn pri branĉa regado. La enirpunkto kovris 99 projektajn modulojn, la strikta kompilo finis 5 008 taskojn, kaj la aksiomkontrolo de 3 383 deklaroj trovis nur `propext`, `Classical.choice`, `Quot.sound`. La negativa regresia testo sukcesis.

## Registrita baza versio

La 10-an de novembro 2026 la publika Ubuntu-rulado por la puŝo de `f867a3016ed872747186faaa61d92ae5b12e6c82` trapasis la striktan kompiladon kaj la aksiomkontrolon, kaj rekonstruis la kvar eldonojn de la artikolo. La Lean-tasko uzis la oficialan Mathlib-kaŝmemoron kaj kompilis la projekton en freŝa rulmedio. La protokolo enhavas la jenajn rezultojn. [Lean-tasko](https://github.com/miuchan/structural-certificates-for-prediction-depth/actions/runs/42731331746/job/129549832955) · [Artikoltasko](https://github.com/miuchan/structural-certificates-for-prediction-depth/actions/runs/42731331746/job/129549833258)

```text
Entry point covers all 96 project modules.
Build completed successfully (4972 jobs).
Audited 3282 project declarations: only propext, Classical.choice, Quot.sound.
Audit regression passed: AuditRegressionExternal.unexpectedTheorem transitively depends on unapproved axiom AuditRegressionDependency.unexpectedOracle.
```

La nombro de kompilaj taskoj inkluzivas dependecojn. La nombro de deklaroj inkluzivas difinojn, teoremojn kaj helpajn deklarojn generitajn de Lean.

Aparta loka rekompilo de la sama enmeto en macOS 26.6.2 (arm64, Python 3.14.5) reproduktis la kvar rezultojn. La elprenita kopio ne enhavis projektajn kompilproduktojn. Ĝi uzis la instalitan Lean-version kaj ekzistantajn kompilproduktojn de la dependecoj. Ĉiuj dek unu dependecaj revizioj kongruis kun la fiksdosiero, kaj iliaj registritaj fontdosieroj estis sen ŝanĝoj. La kontrolo finiĝis sukcese kaj konservis la fiksitajn ilaron kaj dependecajn versiojn.

La kontrolo elektas la deklarojn laŭ la moduloj, en kiuj ili estas difinitaj. `scripts/check_audit.py` kompilas testan teoremon en provizora dosierujo. Ĝia nomspaco malsamas al la difina modulo, kaj ĝi dependas de ekstera aksiomo per meza teoremo. La regresia testo postulas, ke la ordinara kontrolskripto finiĝu kun nenula elirstato kaj raportu la specifitajn teoremon kaj aksiomon.

La laborfluo komparas la SHA de la elprenita enmeto kun tiu de la evento kaj registras ĝin en la rularesumo. Por puŝa evento la SHA identigas la puŝitan enmeton. Por kunigpeto ĝi identigas la kunigan enmeton generitan de GitHub. Por kontroli la rezulton por iu versio, komparu la SHA en la resumo kun la rezulto de `gh run list --commit <SHA>`. [Laborfluo de GitHub Actions](../../../.github/workflows/lean.yml)

## Sendependa reproduktado

Kun Elan, Git kaj Python 3 disponeblaj, rulu la jenon per Bash el freŝa klono de la publika deponejo. Agordu `revision` al la plena SHA de la kontrolata eldono. La procedo uzas la fiksitan Lean-version kaj kompilas la dependecojn el la fiksitaj fontoj kun malŝaltitaj Lake-kaŝmemoroj.

```bash
set -euo pipefail
revision=f867a3016ed872747186faaa61d92ae5b12e6c82
git checkout --detach "$revision"
git rev-parse HEAD
test -z "$(git status --porcelain)"
test ! -e .lake
uname -sm
python3 --version
lean --version
LAKE_NO_CACHE=1 LAKE_CACHE_DIR= ./scripts/check.sh 2>&1 | tee ../prediction-depth-check.log
git diff --exit-code HEAD -- lean-toolchain lakefile.toml lake-manifest.json
```

Por ripeto kun kaŝmemoro, post la komencaj kontroloj rulu `lake exe cache get` kaj poste `./scripts/check.sh`. Registru la kaŝmemoran fonton kaj kontrolu, ke `.lake/build` ankoraŭ ne ekzistas antaŭ la projektkompilo. Ambaŭokaze konservu la SHA, rulmedion, kaŝmemoran politikon kaj kompletan protokolon. Datita raporto, kiu identigas la reviziinton kaj la kontrolitajn teoremajn asertojn, dokumentus sendependan revizion. La publika CI-registro atestas aŭtomatan rekonstruon. Ekstera revizia raporto ankoraŭ ne estas registrita.

La aksiomkontrolo ekzamenas la logikajn aksiomojn uzatajn de la projektaj deklaroj, ankaŭ tra importoj. La kontrolado fidas je la fiksitaj Lean-iloj kaj ilia kerno. Kun kaŝmemoro ĝi fidas ankaŭ je la importitaj kompilproduktoj de la dependecoj. Rekompili la dependecojn el la fontoj forigas tiun dependecon de la kaŝmemoro. La komparo de la formalaj difinoj kun la matematikaj asertoj estas aparta revizia tasko. [Logikaj fundamentoj kaj fidolimoj](dependencies.md)

## Matematika akceptokontrolo

- Por A ekzistas Lean-pruvoj pri la finia cirkvitkonstruo, vojlokaj kondiĉoj, arbitra tutmonda statspaco, unuforma generilo kaj NC-membreco sub kostokondiĉo. La pruvo eksplicite enkalkulas la kopiajn pordegojn de la normaliga unuforma kompililo. Duuma kodo de granda tempo sola estas nesufiĉa por NC-membreco.
- La norma instanco de B uzas efektivajn maŝinojn kaj pruvitan CVP-kompletecon. La projekto pruvas fermitecon de unuforma NC sub ĝeneralaj logspacaj reduktoj kun ŝanĝiĝemlonga eliro. La fina kondiĉa konkludo konservas la eksplicitan supozon `P ≠ NC`.
- La entjera formo `m ≤ b^d`, la logaritma formo kaj la finiaj atestiloj per distingantaj valorasignoj de C estas pruvitaj por cirkvitoj kun komunaj subcirkvitoj.
- La OR-ekzemplo havas pruvitajn statsemantikon, finian enirkodadon, efektivan unuforman generilon, fiksitan polinoman buĝeton, precizan optimuman profundon kaj kongruan malsupran baron por arbitraj cirkvitoj de De Morgan kun komunaj subcirkvitoj. La pruvo kovras tempon nul.
- La matrica ekzemplo super la dukorpa kampo uzas efektivajn XOR- kaj AND-cirkvitojn kun konkretaj baroj por profundo, pordegonombro kaj kompleta priskribogrando. La geometria disvastiĝbaro eksplicite limigas la lokan strukturon de la prognozilo.
- La regulfamilio kun fiksita regado havas koeficientan formulon por arbitra komenca regagordo, vojan kompiladon kaj malkodadon, logaritman supran profundobaron, logspac-unuforman generilon kaj kongruan malsupran baron por la gardoj AND kaj OR. [Modelo kaj amplekso](frozen-pascal.md)
- La profundoklasifiko por fiksita regado donas necesan kaj sufiĉan kondiĉon por unu komuna konstanta profundobaro je ĉiuj tempoj. Variaj gardoj havas logaritman malsupran baron por pordegoj de maksimume du eniroj. La profundobaroj por la homogena Pascal-regulo dependas de la nombro de unubitoj en la tempo. La specialaj cirkvitoj por konstanta profundo kaj por Pascal havas eksplicitajn barojn por la nombro de pordegoj.
- La rulebla klasifikilo resendas rezultojn ekvivalentajn al la kvar semantikaj kondiĉoj. La unuforma klasifika teoremo pruvas lingvan ĝustecon, polinoman pordegonombron kaj la branĉajn profundobarojn por unu efektive generata familio, kaj karakterizas membrecon en norma unuforma NC⁰.
- La modelo kun transportata regado derivas konjunkcion sur finia fenestro el sinkrona evoluo sur senfina krado, precize karakterizas la esencajn enirojn kaj atingas optimuman profundon per cirkvito kun lineara nombro da pordegoj. La kongrua malsupra baro kovras cirkvitajn retojn kun du eniroj po pordego kaj komunaj subcirkvitoj. Tiu rezulto validas por la cirkvitoj de ĉiu aparta tempo. [Lean-teoremo](../../../PredictionDepth/TransportedControl.lean)
- La minimuma profundo de la homogena Pascal-regulo je ĉiu tempo estas $`p`$ kun denaska XOR. En la modelo de De Morgan kun NOT nombrata kiel tavolo, ĝi estas nul por $`p=0`$ kaj $`2p+1`$ por $`p>0`$. La unuforma generilo uzas apartan konstruon kaj donas la supran baron $`3p`$. [Teoremo por denaska XOR](../../../PredictionDepth/FrozenPascal/HomogeneousPascal.lean) · [Teoremo pri De Morgan-profundo](../../../PredictionDepth/FrozenPascal/PascalExactDepth.lean) · [Unuforma generilo](../../../PredictionDepth/FrozenPascal/UniformHomogeneous.lean)
- Kiam unuforma ŝovo de la regado konservas la du datumajn branĉojn, Lean kontrolas la fiksiĝon de la regado en moviĝanta referenca kadro kaj la rekonekton de la finia fenestro post interŝanĝo de la gardoj. La reuzata cirkvito je ĉiu tempo konservas la pordegonombron kaj ne pligrandigas la profundon. [Moviĝanta referenca kadro kaj rimedobaroj](../../../PredictionDepth/TransportedBranching.lean)
- Por la branĉa modelo kun adicia regado, Lean derivas el la sinkrona iteracio la koeficientan formulon kun komuna Pascal-pareco kaj tutnulaj sufiksoj. La artikolo pruvas la linearan pordegonombron kaj la kongruajn logaritmajn profundobarojn. [Iteracia teoremo por adicia regado](../../../PredictionDepth/AdditiveBranching.lean) · [Pruvo en la artikolo](../../../paper/structural-certificates.eo.pdf)

Dum revizio de la teoremaj asertoj, komparu la laborspacan mezuron, finian regadon, nuraldoneblan eliron kaj varilongan eliron kun la norma maŝinmodelo. Kontrolu la kodadon de la demandoj kaj de la tempo, la vojlokajn hipotezojn de A kaj la eksplicitan klasapartigan supozon de B. Por la klasifiko kun fiksita regado, kontrolu, ke ĝusteco, unuformeco, grando kaj la profundaj supraj baroj validas por unu sama cirkvitfamilio, kaj ke la malsupra baro ampleksas ĉiujn prognozilojn en la koncerna modelo. Por la ekzemplo kun transportata regado, kontrolu la projekcion al la finia fenestro kaj la amplekson de la cirkvita baro por ĉiu aparta tempo. [Maŝinmodelo](dependencies.md) · [Formala amplekso](requirements.md)

## Rekonstruado de la artikolo

La tasko `Rebuild paper PDFs` rekonstruas la kvar eldonojn per Typst 0.15.1 kaj Noto Serif CJK 2.003. Ĝi registras la kontrolsumojn en la protokolo kaj la SHA de la enmeto en la rularesumo. Malfermu la PDF-dosieron en GitHub kaj premu `y` por ricevi konstantan ligilon al tiu enmeto. La sama plena SHA identigas la respondajn fontojn en Typst kaj Lean. [Lokaj rekonstruaj instrukcioj](../README.md) · [GitHub-gvidilo pri konstantaj ligiloj](https://docs.github.com/en/repositories/working-with-files/using-files/getting-permanent-links-to-files)

La macOS-rekonstruo de la registrita baza enmeto reproduktis ĉiujn kvar deponejajn PDF-dosierojn bajton post bajto. La Ubuntu-CI de la sama enmeto registris kongruajn SHA-256-sumojn por la angla, simpligita ĉina kaj Esperanta eldonoj, kaj malsaman sumon por la japana. Komparu rekonstruon kun kontrolsumo registrita por la sama platformo. La kvar tipardosieroj uzitaj en macOS kongruis kun la Git-objektoj de la fiksita Noto-enmeto. [Kontrolregistro pri PDF-oj kaj tiparoj](../../../docs/verification.md#paper-rebuild)
