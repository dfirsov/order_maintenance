// Differential test of viz/om.js against the prototype core.
//
//   python3 gen_traces.py DIR && node check.js DIR
//
// Replays every trace of gen_traces.py and compares, after every operation, the new
// element's key, the fallback count, the step count, reservations, drains and the
// digest of all keys. Also checks that keys strictly increase along the list.
"use strict";
const fs = require("fs");
const path = require("path");
const OM = require("../om.js");

const MOD = (1n << 61n) - 1n;
function digest(core) {
  let h = 0n;
  for (const e of core.elements()) for (const v of core.key(e)) h = (h * 1000003n + v) % MOD;
  return h;
}

const dir = process.argv[2];
let bad = 0, total = 0, files = 0;
for (const fn of fs.readdirSync(dir).filter(f => f.endsWith(".json")).sort()) {
  const t = JSON.parse(fs.readFileSync(path.join(dir, fn)));
  const core = new OM.Core(OM.paramsFor(t.N, t.params));
  let err = null;
  for (let i = 0; i < t.ops.length && !err; i++) {
    const [op, x] = t.ops[i];
    let y = null;
    if (op === "i") y = core.insert_after(x, core.E.length); else core.mark_dead(x);
    const [key, fb, steps, res, drains, dig] = t.recs[i];
    const got = [y === null ? null : core.key(y).map(String), core.stats.fallbacks,
                 core.totalSteps(), core.stats.reservations, core.top.drains];
    const want = [key, fb, steps, res, drains];
    if (JSON.stringify(got) !== JSON.stringify(want))
      err = `op ${i}: got ${JSON.stringify(got)}, want ${JSON.stringify(want)}`;
    else if (dig !== null && String(digest(core)) !== dig) err = `op ${i}: digest differs`;
    else if (dig !== null && !core.keysSorted()) err = `op ${i}: keys not increasing`;
    total++;
  }
  files++;
  if (err) { bad++; console.log(`FAIL ${fn}: ${err}`); }
}
console.log(`${files} traces, ${total} operations, ${bad} failing`);
process.exit(bad ? 1 : 0);
