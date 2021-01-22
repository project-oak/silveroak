# AES Verification status

### Phase 1 Essential Tasks

These are the minimum pieces required for a verified AES-256 implementation
(proven against a spec, with a proof that decryption is the inverse of
encryption) without key expansion or AES-192 support.

| component       | task                         | status        |
| --------------- | ---------------------------- | ------------- |
| top-level loop  | write spec                   | done          |
|                 | prove inverse lemma for spec | done          |
|                 | implement circuit            | in progress (see [#413](https://github.com/project-oak/silveroak/pull/413)) |
|                 | prove circuit matches spec   | done          |
| `add_round_key` | write spec                   | done          |
|                 | prove inverse lemma for spec | done          |
|                 | implement circuit            | done          |
|                 | prove circuit matches spec   | done          |
| `sub_bytes`     | write spec                   | done          |
|                 | prove inverse lemma for spec | done          |
|                 | implement circuit            | in progress ([#320](https://github.com/project-oak/silveroak/pull/320)) |
|                 | prove circuit matches spec   | not started ([#463](https://github.com/project-oak/silveroak/pull/463))   |
| `shift_rows`    | write spec                   | done          |
|                 | prove inverse lemma for spec | done          |
|                 | prove spec commutes with `sub_bytes` spec | done          |
|                 | implement circuit            | done          |
|                 | prove circuit matches spec   | not started ([#460](https://github.com/project-oak/silveroak/pull/460))  |
| `mix_columns`   | write spec                   | done          |
|                 | prove inverse lemma for spec | in progress ([#295](https://github.com/project-oak/silveroak/pull/295))    |
|                 | prove spec commutes with `add_round_key` spec | in progress ([#312](https://github.com/project-oak/silveroak/pull/312))        |
|                 | implement circuit            | done          |
|                 | prove circuit matches spec   | not started ([#462](https://github.com/project-oak/silveroak/pull/462))   |
| "glue" plugging subroutines into top-level loop for AES-256 | prove inverse lemma for spec | done   |
|                 | implement circuit            | done   |
|                 | prove circuit matches spec   | done   |
