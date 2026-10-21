# D12 v1：再現記録の主根拠の更新

2026-10-21。mailbox `6046e4bc-5047-4216-9c61-1201db7f20bd` の返事を反映した。**現在の再現の主根拠を、統括の [新しいsummary](d12-independent-repro-2026-10-21.json) に差し替えた**。[claims](D12-v1/claims.json)・[receipt](D12-v1/route_b-receipt.json)・[manifest](D12-v1/source-manifest.json)・[来歴](D12-v1/proof-routes.md)・[本文](paper-D12-v1-en.tex)と入口を更新した。数学の分類、18主張のID／状態、人間査読・Leanなし、盲検の留保は変更していない。

## 確認できたことと、できないこと

| 記録 | 今回の確認 |
|---|---|
| 新しい統括summary | PASS、5検査器が終了0、6比較がEXACT_MATCH。19 source_sha256を含む |
| 提出commit `1c144ca9` との照合 | **18/19が同一**。相違は `mac_memory_guard.py` だけ |
| 監視ツールの相違 | 新summaryのhashは後のcommit `1944a095` のbytesと一致。固定版との差分はtimeout・確認間隔の引数化。検査器の他18ソースは固定版と同じ |
| 証明書の意味の照合 | 新summaryの6 semantic_sha256を、受領済みの証明書からこちらで再計算し、全て一致 |
| 旧T0250の3差 | 履歴として16/19一致を保存。**「RouteBの説明ではsummary保存先の引数化、直接未確認」**と記載。T0250の元ソースbytesがGitにないため、この説明が3ファイルの差を実際に説明するかは直接確認していない |
| こちらの過去の限定再現 | T1490/T1491のlsof timeout、検査器起動前の停止をそのまま保持。監視を迂回した／自前再現が成功したとはしない |

新summaryは**統括による実行の記録**で、こちらが今回検査器を再実行したものではない。今回も科学計算の検査器起動・Lean・公開操作は0。verifyへの書込みやmergeは行わず、監視ツールはGitの固定オブジェクトを読んでhashと差分を確認しただけで、実行していない。

## 保存と検査

- 前回のPDF・送付済み報告書を変更していない。更新前のclaims／receipt／manifest／本文などを [履歴](D12-v1/history-2026-10-20/) に保存。追記された統括点検文書の旧bytesも保存し、旧hashと現在のhashを混同しない。[更新計画](D12-provenance-update-plan-2026-10-21.json)。
- 本文の要旨・再現段落・来歴の留保・次の点検の説明を更新。新しいPDFは `data/cache/Study/D12-draft-v1-provenance-2026-10-21/paper-D12-v1-en.pdf`。[pdf-validation](D12-v1/pdf-validation.json) にhashを保存。T1499組版・T1500 render、**10頁全て目視**、overflow／未定義参照0。
- T1501の**公開用／内部用走査は13ファイル・1 PDF、両方検出0件**。新summaryを含むpresentationが対象。非公開識別子表・生の受領資料・内部trialログは含めない。[走査receipt](D12-v1/privacy-validation.json)。
- T1504の [整合性検査](D12-v1-validation.json) PASS。新summaryの18同一＋監視道具1差、6証明書、旧T0250の保持、旧PDFのhash、18主張のID／状態と番号付き主張文の一致、**12拒否対照**を確認した。新summaryを旧記録へ戻す／新summaryをevidenceから落とす誤りも拒否する。更新スクリプトの構文ミスで止まったT1502/T1503も保存し、修正後の成功と区別した。

この更新は来歴の訂正であり、証明を新たに査読・形式化したものではない。T0250の説明の直接確認、数学の人間査読、新規性の確定は完了していない。30分の枠内でcommitし、この報告をmailboxで一度統括へ渡す。次の大きな作業は朝の本人判断を待つ。
