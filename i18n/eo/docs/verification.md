# Kontrolregistro

[English](../../../docs/verification.md) · [简体中文](../../zh-CN/docs/verification.md) · [日本語](../../ja/docs/verification.md) · **Esperanto**

La projekto fiksas Lean al `v4.36.0-rc2` kaj fiksas la [versiojn de la dependecoj](dependencies.md). Rulu la jenan komandon el la deponeja radiko.

```sh
./scripts/check.sh
```

La skripto kontrolas la modulan kovradon de la defaŭlta enirejo, rulas `lake build --wfail`, kontrolas la transitivajn aksiomajn dependecojn de la projektaj deklaroj kaj rulas negativan regresian teston.

```text
Entry point covers all 96 project modules.
Build completed successfully (4972 jobs).
Audited 3282 project declarations: only propext, Classical.choice, Quot.sound.
Audit regression passed: AuditRegressionExternal.unexpectedTheorem transitively depends on unapproved axiom AuditRegressionDependency.unexpectedOracle.
```

La nombro de kompilaj taskoj inkluzivas dependecojn. La nombro de deklaroj inkluzivas difinojn, teoremojn kaj helpajn deklarojn generitajn de Lean.

La kontrolo elektas la deklarojn laŭ la moduloj, en kiuj ili estas difinitaj. `scripts/check_audit.py` kompilas en provizora dosierujo projektan teoremon en alia nomspaco, kiu dependas de ekstera aksiomo per meza teoremo. La regresia testo postulas, ke la ordinara kontrolskripto finiĝu kun nenula elirstato kaj raportu la specifitajn teoremon kaj aksiomon.

La [laborfluo de GitHub Actions](../../../.github/workflows/lean.yml) rulas la saman skripton en Ubuntu. Puŝa evento kontrolas la puŝitan enmeton, kaj kuniga peto kontrolas la kunigan enmeton generitan de GitHub. La laborfluo komparas la SHA de la elprenita enmeto kun tiu de la ekiginta enmeto kaj, ĉe sukceso, registras la SHA en la rularesumo. `gh run list --commit <SHA>` trovas la respondajn publikajn registrojn.

La tasko `Rebuild paper PDFs` rekonstruas la kvar eldonojn per Typst 0.15.1 kaj Noto Serif CJK 2.003. Ĝi registras la kontrolsumojn en la protokolo kaj la SHA de la enmeto en la rularesumo. Malfermu la PDF-dosieron en GitHub kaj premu `y` por ricevi konstantan ligilon al tiu enmeto. La sama plena SHA identigas la respondajn fontojn en Typst kaj Lean. [Lokaj rekonstruaj instrukcioj](../README.md) · [GitHub-gvidilo pri konstantaj ligiloj](https://docs.github.com/en/repositories/working-with-files/using-files/getting-permanent-links-to-files)

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

Sendependa revizio kontrolis ankaŭ la mezuron de efektiva laborspaco, la nuraldoneblan eliron, la finian regadon, ŝanĝiĝemlongajn elirojn, la kanonan tempobitĉenon, la diferencon inter vojaj kaj tutmondaj kondiĉoj kaj la postulon, ke unu sama cirkvitfamilio plenumu la kondiĉojn pri unuformeco, grando kaj profundo. [Logika fundamento kaj fidolimoj de la triapartiaj kompilproduktoj](dependencies.md)
