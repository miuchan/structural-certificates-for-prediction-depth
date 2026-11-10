# Dependecoj, modeloj kaj fidolimoj

[English](../../../docs/dependencies.md) · [简体中文](../../zh-CN/docs/dependencies.md) · [日本語](../../ja/docs/dependencies.md) · **Esperanto**

`lean-toolchain`, `lakefile.toml` kaj `lake-manifest.json` fiksas la reprodukteblan version de la projekto.

| Dependeco | Fiksita versio | Rolo |
| --- | --- | --- |
| Lean | `v4.36.0-rc2`, `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a` | Kerna kontrolo de pruvterminoj |
| cslib-frontier | `3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d` | Konkreta kompleksecteorio, kompililoj por Turing-maŝinoj kaj cirkvitkodado |
| CSLib | `254e30e6d4299c51323aaeaf5f51a4763b375d4a` | Finia regado, multbendaj Turing-maŝinoj kaj ĝeneralaj komputmodeloj |
| Mathlib | `69552756cd8a2d2d48763cf7279fd814d6a1224d` | Matematikaj fundamentoj, matricoj, finiaj aroj kaj logaritmoj de naturaj nombroj |

Triapartia kodo devenas de la fiksita versio de la [fonto de cslib-frontier](https://github.com/cslib-community/cslib-frontier/tree/3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d) kaj de ĝia dependecgrafeo. Formalaj pruvterminoj establas CVP-kompletecon, fermitecon de logspacaj funkcioj sub kunmeto kaj la inkluzivon de NC en P.

## Norma maŝinmodelo

La norma tavolo `PredictionDepth.StandardComplexity` uzas multbendajn Turing-maŝinojn kun finia regado, fiksa nombro da laborbendoj kaj duuma alfabeto. Ĉiu paŝo povas legi la nunajn simbolojn sur la enira kaj laboraj bendoj, movi la kapojn, ŝanĝi la lokajn laborsimbolojn kaj eligi maksimume unu simbolon. La eniro estas nurlegebla kaj la eliro estas nuraldonebla kaj nelegebla por la komputado.

Laborspaco estas mezurata per la nombro de laborbendaj ĉeloj efektive vizititaj en prefikso de la rulado. `ComputableInLogSpace` postulas halton kaj logaritman laborspacon. Polinoma tempo kaj polinoma elirlongo sekvas aparte el la baro por la nombro de finiaj konfiguracioj.

Norma CVP uzas cirkvitinstancojn kun pruvo de valideco kaj injektivan duuman kodadon. Ĝia P-malfacileca teoremo kvantigas super ĉiuj koditaj fontoproblemoj, inkluzive de ĉiuj duumaj vortoj kun identa kodigo. Ĝi do aplikiĝas al la prognoza lingvo de la projekto, kiu estas difinita sur ĉiuj demandovortoj. La lingvo eksplicite malakceptas nevalidajn demandojn.

Unuforma NC postulas, ke unu sama cirkvitfamilio samtempe plenumu semantikajn, grandecajn, profundajn kaj efektivajn logspacajn generkondiĉojn. La klaso P uzas efektivajn maŝinojn de polinoma tempo. `NCClosure` pruvas en la projekto fermitecon sub ĝeneralaj logspacaj reduktoj kun ŝanĝiĝema elirlongo.

## Fundamentaj pruvoj aldonitaj en la projekto

- Efektivaj unuformaj najbarecaj cirkvitoj por konfiguraciaj grafeoj, plej mallongaj vojoj en finiaj direktitaj grafeoj, ripeta kvadratigo de buleaj rilatoj kaj baro de kvadrat-logaritma profundo.
- Flua logspaca grupa traktado por arbitra polinoma grado, kun la origina eniro sur nurlegebla bendo kaj rekomputado de mezaj eliroj sen konservi la tutan rezulton de la grupo.
- Efektiva logspaca seria kaj paralela kunmeto, enkodigo de fiksaj datumoj kaj flua generado de cirkvitfamilioj kun diversgrandaj blokoj.
- `NL ⊆ uniform NC²`, `uniform NC ⊆ P`, fermiteco de unuforma NC sub ĝeneralaj logspacaj reduktoj kaj nemembreco de P-malfacilaj problemoj en unuforma NC sub `P ≠ NC`.

## Kion certigas la kontrolo

`scripts/check_imports.py` postulas, ke la defaŭlta enirmodulo kovru ĉiujn projektajn pruvdosierojn. `lake build` kompilas ĉiujn projektajn modulojn. `Audit.lean` elektas deklarojn laŭ iliaj difinaj moduloj, inkluzive de helpaj deklaroj generitaj de Lean en aliaj nomspacoj. La kontrolo inspektas ĉiun transitivan aksioman dependecon kaj akceptas nur `propext`, `Classical.choice` kaj `Quot.sound`.

Kaŝmemoroj de Mathlib kaj la aliaj kontraŭfluaj bibliotekoj povas rapidigi la kompiladon. Importitaj kompilproduktoj estas parto de la fidbazo same kiel ĉiu alia Lean-dependeco. Por sendependa rekompilado oni povas purigi la dependecajn kompilproduktojn kaj rekonstrui el la fiksitaj fontversioj sen kaŝmemoro. La aksioma kontrolo kontrolas logikajn dependecojn. La fonta dokumentado, eksplicitaj supozoj kaj postularo ebligas apartan kontrolon de la matematikaj difinoj.
