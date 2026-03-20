import { useState, useEffect, useCallback, useMemo, useRef } from "react";

// ─── HOLIDAYS ─────────────────────────────────────────────────────────────────
const HOLIDAYS = new Set([
  "2026-01-01","2026-01-26","2026-03-04","2026-04-03","2026-05-01",
  "2026-05-27","2026-08-28","2026-09-04","2026-09-14","2026-10-02",
  "2026-10-20","2026-11-09","2026-11-11","2026-12-25",
]);

function isWorkday(d) {
  const dt = new Date(d); const day = dt.getDay();
  if (day === 0 || day === 6) return false;
  return !HOLIDAYS.has(dt.toISOString().split("T")[0]);
}
function networkDays(start, end) {
  if (!start || !end) return 0;
  const s = new Date(start), e = new Date(end);
  if (s >= e) return 0;
  let count = 0; const cur = new Date(s); cur.setDate(cur.getDate()+1);
  while (cur <= e) { if (isWorkday(cur)) count++; cur.setDate(cur.getDate()+1); }
  return count;
}
function delayCalendarDays(originalEnd, revisedEnd) {
  if (!originalEnd || !revisedEnd) return 0;
  return Math.round((new Date(revisedEnd)-new Date(originalEnd))/86400000);
}
function calDays(start, end) {
  if (!start||!end) return 0;
  return Math.max(0, Math.round((new Date(end)-new Date(start))/86400000));
}
function addCalendarDays(startDate, days) {
  if (!startDate) return startDate;
  const d = new Date(startDate); d.setDate(d.getDate()+days); return fmtDate(d);
}
function subtractCalendarDays(endDate, days) {
  if (!endDate) return endDate;
  const d = new Date(endDate); d.setDate(d.getDate()-days); return fmtDate(d);
}
function addWorkdays(startDate, wds) {
  if (!startDate) return startDate;
  const d = new Date(startDate); if (isNaN(d)) return startDate;
  if (wds===0) return fmtDate(d);
  let count=0;
  while (count<wds) { d.setDate(d.getDate()+1); if (isWorkday(d)) count++; }
  return fmtDate(d);
}
function fmtDate(d) {
  if (!d) return ""; const dt=new Date(d); if (isNaN(dt)) return "";
  return dt.getFullYear()+"-"+String(dt.getMonth()+1).padStart(2,"0")+"-"+String(dt.getDate()).padStart(2,"0");
}
function fmtDisplay(d) {
  if (!d) return "—"; const dt=new Date(d); if (isNaN(dt)) return "—";
  return dt.toLocaleDateString("en-IN",{day:"2-digit",month:"short",year:"numeric"});
}
function todayStr() { return fmtDate(new Date()); }

// ─── COLORS ───────────────────────────────────────────────────────────────────
const FN_COLORS = {
  "Product":               {bg:"#EDE9FE",border:"#7C3AED",text:"#5B21B6"},
  "Category":              {bg:"#DBEAFE",border:"#2563EB",text:"#1D4ED8"},
  "Design":                {bg:"#FCE7F3",border:"#DB2777",text:"#9D174D"},
  "Finance/Category":      {bg:"#D1FAE5",border:"#059669",text:"#065F46"},
  "Procurement - RM & PM": {bg:"#FEF3C7",border:"#D97706",text:"#92400E"},
  "Production":            {bg:"#FFE4E6",border:"#DC2626",text:"#991B1B"},
  "Overall Launch Plan":   {bg:"#E0F2FE",border:"#0284C7",text:"#075985"},
};
const ST_COLORS = {
  "Done":        {bg:"#D1FAE5",text:"#065F46"},
  "In-progress": {bg:"#FEF3C7",text:"#92400E"},
  "Not Started": {bg:"#F3F4F6",text:"#374151"},
  "Delayed":     {bg:"#FFE4E6",text:"#991B1B"},
};

function getEffectiveEnd(row) {
  if (row && row.revEnd && row.revEnd > row.end) return row.revEnd;
  return row ? row.end : null;
}

// ─── DYNAMIC CRITICAL PATH + FLOAT ANALYSIS ─────────────────────────────────
// Standard PM definition: critical = float of exactly 0.
// Forward pass (EF) + backward pass (LS) + float = LS - EF.
// cpIds  = all rows where float == 0  (any delay pushes go-live).
// nearCriticalIds = float > 0 and <= 14 days.
// topoOrder stored on return so flowchart can use it for correct sequencing.
function computeCriticalPath(rows) {
  if (!rows.length) return { cpIds: new Set(), nearCriticalIds: new Set(), floatById: {}, topoIds: [] };

  const idToRow = {}, successors = {}, inDegree = {};
  rows.forEach(r => { idToRow[r.id] = r; successors[r.id] = []; inDegree[r.id] = 0; });
  rows.forEach(r => {
    [r.depId, r.dep2Id].forEach(pid => {
      if (pid != null && idToRow[pid]) {
        successors[pid].push(r.id);
        inDegree[r.id]++;
      }
    });
  });

  // Topological sort (Kahn's algorithm)
  const queue = rows.filter(r => inDegree[r.id] === 0).map(r => r.id);
  const topoIds = [];
  const deg = {...inDegree};
  while (queue.length) {
    const cur = queue.shift(); topoIds.push(cur);
    (successors[cur]||[]).forEach(sid => { deg[sid]--; if (deg[sid]===0) queue.push(sid); });
  }

  // Forward pass: Earliest Finish (EF) for each node
  const ef = {};
  rows.forEach(r => { ef[r.id] = r.start || todayStr(); });
  topoIds.forEach(id => {
    const row = idToRow[id]; if (!row) return;
    let bestStart = row.start || todayStr();
    [row.depId, row.dep2Id].forEach(pid => {
      if (pid == null || !idToRow[pid]) return;
      const predEnd = ef[pid] || idToRow[pid].end || idToRow[pid].start || todayStr();
      if (predEnd > bestStart) bestStart = predEnd;
    });
    const td = row.totalDays || 0;
    ef[id] = td > 0 ? addCalendarDays(bestStart, td) : bestStart;
  });

  // Project end = latest EF across all nodes
  let latestFinish = '';
  rows.forEach(r => { const f = ef[r.id]||''; if (f > latestFinish) latestFinish = f; });

  // Backward pass: Latest Start (LS) for each node
  const ls = {};
  rows.forEach(r => { ls[r.id] = latestFinish; });
  [...topoIds].reverse().forEach(id => {
    const row = idToRow[id]; if (!row) return;
    const succs = successors[id]||[];
    if (!succs.length) { ls[id] = latestFinish; return; }
    let minLS = latestFinish;
    succs.forEach(sid => {
      const succRow = idToRow[sid]; if (!succRow) return;
      const sls = subtractCalendarDays(ls[sid], succRow.totalDays || 0);
      if (sls < minLS) minLS = sls;
    });
    ls[id] = minLS;
  });

  // Float = LS - EF (calendar days). Float == 0 means critical.
  const floatById = {}, cpIds = new Set(), nearCriticalIds = new Set();
  const NEAR_THRESH = 14;
  rows.forEach(r => {
    const efD = ef[r.id] || r.end || todayStr();
    const lsD = ls[r.id] || latestFinish;
    const fl = Math.max(0, Math.round((new Date(lsD) - new Date(efD)) / 86400000));
    floatById[r.id] = fl;
    if (fl === 0) {
      cpIds.add(r.id);
    } else if (fl <= NEAR_THRESH && r.depId != null) {
      nearCriticalIds.add(r.id);
    }
  });

  // Safety: if nothing got float=0 (disconnected graph), fall back to terminal nodes
  if (cpIds.size === 0) {
    rows.filter(r => !(successors[r.id]||[]).length).forEach(r => cpIds.add(r.id));
  }

  return { cpIds, nearCriticalIds, floatById, topoIds };
}


// ─── CASCADE + CRITICAL PATH ─────────────────────────────────────────────────
// Helper: find all ancestor IDs of a given row (rows that lead to it upstream)
function getAncestors(targetId, rows) {
  const idToRow = {};
  rows.forEach(r => { idToRow[r.id] = r; });
  const ancestors = new Set();
  const stack = [targetId];
  while (stack.length) {
    const cur = stack.pop();
    const row = idToRow[cur]; if (!row) continue;
    [row.depId, row.dep2Id].forEach(pid => {
      if (pid != null && !ancestors.has(pid)) {
        ancestors.add(pid);
        stack.push(pid);
      }
    });
  }
  return ancestors;
}

function cascadeAndCP(rows) {
  const arr = rows.map(r => ({...r}));
  const idxById = {};
  arr.forEach((r,i) => { idxById[r.id] = i; });

  // ── 6-pass cascade: handles both depId and dep2Id ────────────────────────
  // Extra passes ensure long chains AND dep2 branches both converge fully
  for (let pass = 0; pass < 8; pass++) {
    let changed = false;
    for (let i = 0; i < arr.length; i++) {
      const row = arr[i];
      const deps = [row.depId, row.dep2Id].filter(d => d != null);
      if (!deps.length) continue;
      // Find the latest effective-end among ALL predecessors (dep + dep2)
      let latestEnd = null;
      deps.forEach(pid => {
        const di = idxById[pid]; if (di == null) return;
        const de = getEffectiveEnd(arr[di]); if (!de) return;
        if (!latestEnd || de > latestEnd) latestEnd = de;
      });
      if (!latestEnd || row.start === latestEnd) continue;
      const newStart = latestEnd;
      const newEnd = row.totalDays > 0 ? addCalendarDays(newStart, row.totalDays) : newStart;
      arr[i] = { ...row, start: newStart, end: newEnd,
        workingDays: networkDays(newStart, newEnd),
        delayDays: row.revEnd ? delayCalendarDays(newEnd, row.revEnd) : null };
      changed = true;
    }
    if (!changed) break; // converged early
  }

  // ── Option C: go-live gate ───────────────────────────────────────────────
  // Going Live on D2C should not precede any of its upstream ancestors.
  // Find the "Going Live on D2C" row and push its date if any ancestor ends later.
  const goLiveIdx = arr.findIndex(r => r.task === "Going Live on D2C");
  if (goLiveIdx >= 0) {
    const glRow = arr[goLiveIdx];
    // All ancestors of Going Live on D2C (excludes downstream like Dispatch POs)
    const ancestors = getAncestors(glRow.id, arr);
    let latestAncestorEnd = glRow.start || "";
    ancestors.forEach(aid => {
      const ai = idxById[aid]; if (ai == null) return;
      const ae = getEffectiveEnd(arr[ai]) || arr[ai].end || "";
      if (ae > latestAncestorEnd) latestAncestorEnd = ae;
    });
    // If any ancestor ends after current go-live start, push go-live forward
    if (latestAncestorEnd > (glRow.start || "")) {
      arr[goLiveIdx] = {
        ...glRow,
        start: latestAncestorEnd,
        end: latestAncestorEnd, // td:0 so start=end
        workingDays: 0,
      };
    }
  }

  // ── Re-resolve depEnd rows after cascade + go-live gate ───────────────────
  // depEnd rows (e.g. IG halt, IG Pre-launch, KV Moodboard) anchor their END to
  // another row's START. After dates shift, re-run the back-calc so they stay correct.
  const idToArrRow = {};
  arr.forEach(r => { idToArrRow[r.id] = r; });
  for (let iter = 0; iter < 6; iter++) {
    let changed = false;
    for (let i = 0; i < arr.length; i++) {
      const row = arr[i];
      if (row.depEnd == null) continue;
      const anchorRow = idToArrRow[row.depEnd];
      if (!anchorRow) continue;
      const newEnd = anchorRow.start;
      if (!newEnd) continue;
      const newStart = row.totalDays > 0
        ? subtractCalendarDays(newEnd, row.totalDays) : newEnd;
      if (row.start === newStart && row.end === newEnd) continue;
      arr[i] = { ...row, start: newStart, end: newEnd,
        workingDays: networkDays(newStart, newEnd) };
      idToArrRow[row.id] = arr[i];
      changed = true;
    }
    if (!changed) break;
  }

  // ── Recompute CP + float on final dates ──────────────────────────────────
  const { cpIds, nearCriticalIds, floatById, topoIds } = computeCriticalPath(arr);
  return arr.map(r => ({
    ...r,
    isCritical: cpIds.has(r.id),
    isNearCritical: nearCriticalIds.has(r.id),
    floatDays: floatById[r.id] != null ? floatById[r.id] : null,
    topoOrder: topoIds.indexOf(r.id),
  }));
}


// ─── ISOLATE TEMPLATE ─────────────────────────────────────────────────────────
// td = Total Days (calendar, exact from Excel)
// wd = Working Days (exact from Excel, used only for display — end always = start + td)
// dep = template index of predecessor (this row's start = predecessor's effectiveEnd)
// depEnd = this row's END = row[depEnd]'s START (back-calc: start = end - td)
// depElse = fallback dep if primary dep filtered out in New Project builder
const ISOLATE_TEMPLATE = [
  // 0-5 Product NPD
  {fn:"Product",sf:"NPD",task:"Product Version 1",spoc:"Rachna/Priyanka",td:7,wd:5,dep:null,status:"Done"},
  {fn:"Product",sf:"NPD",task:"Consumer Tastings 1",spoc:"Rachna/Priyanka",td:5,wd:3,dep:0,status:"Done",remarks:"Check for feedback form verbatim/ responses"},
  {fn:"Product",sf:"NPD",task:"Product Version 2",spoc:"Rachna/Priyanka",td:7,wd:5,dep:1,status:"Done"},
  {fn:"Product",sf:"NPD",task:"Consumer Tastings 2",spoc:"Rachna/Priyanka",td:15,wd:10,dep:2,status:"In-progress",remarks:"Priyanka has restarted the process"},
  {fn:"Product",sf:"NPD",task:"Recipe Lock",spoc:"Rachna/Priyanka",td:4,wd:3,dep:3,status:"Not Started"},
  {fn:"Product",sf:"NPD",task:"Lab tests (BOP + Label Mandate Sheet Finalize + Shelf Life test)",spoc:"Rachna/Priyanka",td:30,wd:20,dep:4,status:"Not Started"},
  // 6-9 Category
  {fn:"Category",sf:"Category",task:"Packaging Format",spoc:"Dhvanil/Shrey",td:4,wd:2,dep:null,status:"Done",remarks:"Unflavoured Isolate package - Minimal but more data / beginner friendly"},
  {fn:"Category",sf:"Category",task:"Transit Test - New Packaging Structure (if needed)*",spoc:"Baskaran/Shrey",td:0,wd:0,dep:6,isOptional:true,status:"Not Started",remarks:"Not needed for this; 15 days TAT for round 1"},
  {fn:"Category",sf:"Category",task:"SKU Mix",spoc:"Dhvanil/Shrey",td:1,wd:1,dep:6,status:"Done",remarks:"Only 1kg pouch for now."},
  {fn:"Category",sf:"Category",task:"Consumer work - Functional Pro vs Lifestyle user",spoc:"Dhvanil/Shrey",td:25,wd:20,dep:6,status:"Done",remarks:"Ongoing, not impacting network timelines"},
  // 10-27 Design Pouch Packaging
  {fn:"Design",sf:"Pouch Packaging",task:"Core proposition decision",spoc:"Dhvanil/Shrey",td:3,wd:3,dep:6,status:"Done",remarks:"Previous packs from TOD; BD note on Isolight approach"},
  {fn:"Design",sf:"Pouch Packaging",task:"Shashank's feedback",spoc:"Shashank",td:5,wd:3,dep:10,status:"Done"},
  {fn:"Design",sf:"Pouch Packaging",task:"Brief to TOD",spoc:"Dhvanil/Shrey",td:2,wd:2,dep:11,status:"Done",remarks:"Potential Delay due to NG prep"},
  {fn:"Design",sf:"Pouch Packaging",task:"V1 of Pouch Artwork",spoc:"Shreya",td:7,wd:5,dep:12,status:"Done",remarks:"TOD still working on V1 pack"},
  {fn:"Design",sf:"Pouch Packaging",task:"Feedback from Category + Consumer work pov share",spoc:"Dhvanil/Shrey",td:1,wd:1,dep:13,status:"Done"},
  {fn:"Design",sf:"Pouch Packaging",task:"V2 of Pouch Artwork",spoc:"Shreya",td:7,wd:4,dep:14,status:"Done"},
  {fn:"Design",sf:"Pouch Packaging",task:"Feedback from Shashank/Dhvanil",spoc:"TOD/Shashank",td:4,wd:2,dep:15,status:"Done"},
  {fn:"Design",sf:"Pouch Packaging",task:"V3 of Pouch Artwork",spoc:"Shreya",td:7,wd:5,dep:16,status:"In-progress"},
  {fn:"Design",sf:"Pouch Packaging",task:"Feedback from Shashank/Dhvanil (V3)",spoc:"TOD/Shashank",td:4,wd:4,dep:17,status:"Not Started"},
  {fn:"Design",sf:"Pouch Packaging",task:"V4 of Pouch Artwork",spoc:"Shreya",td:5,wd:3,dep:18,status:"Not Started"},
  {fn:"Design",sf:"Pouch Packaging",task:"Feedback on V4 artwork from QC/Regulatory",spoc:"Regulatory",td:4,wd:3,dep:19,status:"Not Started"},
  {fn:"Design",sf:"Pouch Packaging",task:"Feedback from Shashank/Dhvanil (V4)",spoc:"TOD/Shashank",td:0,wd:0,dep:20,status:"Not Started"},
  // BOP: dep:5 (Lab tests) when Product present; depElse:21 (V4 feedback) when Product absent
  {fn:"Design",sf:"Pouch Packaging",task:"BOP + Label Mandate Sheet sent to TOD (readable format)",spoc:"Dhvanil/Shrey",td:1,wd:1,dep:5,depElse:21,status:"Not Started"},
  {fn:"Design",sf:"Pouch Packaging",task:"V5 of Pouch Artwork",spoc:"Shreya",td:6,wd:4,dep:22,status:"Not Started"},
  {fn:"Design",sf:"Pouch Packaging",task:"Colored Prints & Mockups of V4 of Pouch Artwork",spoc:"Komal/Shrey",td:7,wd:4,dep:23,status:"Not Started"},
  {fn:"Design",sf:"Pouch Packaging",task:"Approval on V5 artwork from QC/Regulatory",spoc:"QC/Shrey",td:7,wd:4,dep:23,status:"Not Started"},
  {fn:"Design",sf:"Pouch Packaging",task:"Feedback from Shashank/Dhvanil (V5)",spoc:"TOD/Shashank",td:2,wd:2,dep:25,status:"Not Started"},
  {fn:"Design",sf:"Pouch Packaging",task:"Final Artwork Handover",spoc:"Shreya",td:3,wd:2,dep:26,status:"Not Started"},
  // 28-29 Finance/Category
  {fn:"Finance/Category",sf:"Pricing",task:"P&L / GM statement",spoc:"Shrey",td:7,wd:5,dep:4,status:"Not Started"},
  {fn:"Finance/Category",sf:"Pricing",task:"Finalize channel & SKU mix based PL",spoc:"Vinit/Dhvanil/Shrey",td:3,wd:2,dep:28,status:"Not Started"},
  // 30-34 Category DP
  {fn:"Category",sf:"DP",task:"V1 Ambition demand plan - First cut assumptions",spoc:"Dhvanil/Shrey",td:3,wd:2,dep:29,status:"Not Started"},
  {fn:"Category",sf:"DP",task:"Frontend meet - Setup all channels meeting for alignment",spoc:"Shrey",td:1,wd:0,dep:30,status:"Not Started",remarks:"N-2 consensus forecast meeting alignment"},
  {fn:"Category",sf:"DP",task:"Backend meet - Setup production, procurement and ops team",spoc:"Shrey",td:1,wd:0,dep:31,status:"Not Started"},
  {fn:"Category",sf:"DP",task:"Revisions to DP basis meetings",spoc:"Shrey",td:7,wd:5,dep:32,status:"Not Started"},
  {fn:"Category",sf:"DP",task:"Share network mail to all channel owners",spoc:"Shrey",td:3,wd:3,dep:33,status:"Not Started"},
  // 35-39 Category Pouch Renders (after Final Artwork Handover dep:27)
  {fn:"Category",sf:"Pouch Renders",task:"Share pouch artwork for renders",spoc:"Shrey",td:2,wd:1,dep:27,status:"Not Started"},
  {fn:"Category",sf:"Pouch Renders",task:"V1 of pouch renders",spoc:"Shrey",td:10,wd:8,dep:35,status:"Not Started"},
  {fn:"Category",sf:"Pouch Renders",task:"Feedback from Category",spoc:"Shrey",td:1,wd:1,dep:36,status:"Not Started"},
  {fn:"Category",sf:"Pouch Renders",task:"V2 of renders",spoc:"Shrey",td:7,wd:4,dep:37,status:"Not Started"},
  {fn:"Category",sf:"Pouch Renders",task:"Approved Pouch Renders",spoc:"Shrey",td:3,wd:1,dep:38,status:"Not Started"},
  // 40-42 Category NPI Details
  {fn:"Category",sf:"NPI Details",task:"Get HSN Code",spoc:"Shrey",td:3,wd:3,dep:35,status:"Not Started"},
  {fn:"Category",sf:"NPI Details",task:"Create Unicomm codes for all SKUs",spoc:"Amit/Shrey",td:2,wd:1,dep:40,status:"Not Started"},
  {fn:"Category",sf:"NPI Details",task:"Share NPI Details with all Q-Com",spoc:"Shrey",td:4,wd:4,dep:39,status:"Not Started"},
  // 43-47 Procurement
  {fn:"Procurement - RM & PM",sf:"Vendor orders",task:"New supplier onboarding and assurance check (if needed)*",spoc:"Baskaran/Rachna",td:0,wd:0,dep:4,isOptional:true,status:"Not Started",remarks:"Not needed for this; 7-10 days TAT"},
  {fn:"Procurement - RM & PM",sf:"Vendor orders",task:"Place order for RM as per demand plan",spoc:"Rachna",td:2,wd:2,dep:34,status:"Not Started",remarks:"Connect with Ayushi/Anirudh"},
  {fn:"Procurement - RM & PM",sf:"Vendor orders",task:"Colour and text proofing for PM with vendor",spoc:"Komal/Shrey",td:4,wd:3,dep:27,status:"Not Started"},
  {fn:"Procurement - RM & PM",sf:"Vendor orders",task:"Place order for pouch primary packaging",spoc:"Komal/Shrey",td:2,wd:2,dep:45,status:"Not Started"},
  {fn:"Procurement - RM & PM",sf:"Vendor orders",task:"Pouch primary packaging arrives",spoc:"Komal/Shrey",td:31,wd:31,dep:46,status:"Not Started"},
  // 48-55 Production
  {fn:"Production",sf:"RM Stock-buildup",task:"Connect RM to barkhana",spoc:"NPD Team",td:20,wd:16,dep:44,status:"Not Started"},
  {fn:"Production",sf:"Approval",task:"Quality Approval - RM",spoc:"NPD Team",td:2,wd:2,dep:48,status:"Not Started"},
  {fn:"Production",sf:"Approval",task:"Quality Approval - PM (Pouches)",spoc:"Samiksha",td:2,wd:2,dep:47,status:"Not Started"},
  {fn:"Production",sf:"Quality Specs",task:"SOP + BOM + FG specs + Checklist from QA + TESTs",spoc:"Urvashi",td:4,wd:4,dep:50,status:"Not Started"},
  {fn:"Production",sf:"Quality Specs",task:"SOP process construction and approval",spoc:"Urvashi",td:1,wd:1,dep:50,status:"Not Started"},
  {fn:"Production",sf:"Trial Run",task:"Production Trial Run + Training",spoc:"NPD Team",td:0,wd:0,dep:51,status:"Not Started"},
  {fn:"Production",sf:"Trial Run",task:"BBK Stock Run",spoc:"NPD Team",td:3,wd:2,dep:53,status:"Not Started"},
  {fn:"Production",sf:"Stock-buildup",task:"Connect FG to forward warehouses",spoc:"Yash",td:7,wd:6,dep:54,status:"Not Started"},
  // 56-59 Category Shoot
  // KV Moodboard: depEnd:58 means its END = Shoot Day's START; start = end - 35 calendar days
  {fn:"Category",sf:"Marketing Messages",task:"KV Moodboard Finalisation",spoc:"Shrey",td:35,wd:24,dep:null,depEnd:58,status:"Not Started"},
  {fn:"Category",sf:"Product Samples",task:"Pouch Samples for Shoot",spoc:"Shrey",td:10,wd:10,dep:45,status:"Not Started",remarks:"Samples from pouch packaging vendor"},
  {fn:"Category",sf:"Photo Shoot",task:"Shoot Day",spoc:"Media Labs Team",td:5,wd:3,dep:57,status:"Not Started",remarks:"Samples as requested from pouch packaging vendor"},
  {fn:"Category",sf:"Photo Shoot",task:"Receiving Edited Images",spoc:"Media Labs Team",td:14,wd:9,dep:58,status:"Not Started"},
  // 60-66 Overall Launch Plan - Marketing
  {fn:"Overall Launch Plan",sf:"Marketing Messages",task:"Q-Com listing images",spoc:"Media Labs Team",td:10,wd:8,dep:59,status:"Not Started"},
  {fn:"Overall Launch Plan",sf:"Marketing Messages",task:"D2C listing images",spoc:"Media Labs Team",td:10,wd:8,dep:59,status:"Not Started",remarks:"Finalize assets"},
  {fn:"Overall Launch Plan",sf:"Marketing Messages",task:"Amazon listing images + A+",spoc:"Media Labs Team",td:10,wd:8,dep:59,status:"Not Started"},
  // IG brief & Website brief: depEnd:58 (end = Shoot Day start); start = end - 15 cal days
  {fn:"Overall Launch Plan",sf:"Marketing Messages",task:"IG launch post caption brief to Samarth",spoc:"Shrey",td:15,wd:11,dep:null,depEnd:58,status:"Not Started"},
  {fn:"Overall Launch Plan",sf:"Marketing Messages",task:"Website copy brief to Samarth",spoc:"Shrey",td:15,wd:11,dep:null,depEnd:58,status:"Not Started"},
  // Final KV: dep:59 (Receiving Edited Images)
  {fn:"Overall Launch Plan",sf:"Marketing Messages",task:"Final new KV + IG Pre-Launch and Final Launch Post Finalisation",spoc:"Media Labs Team",td:20,wd:15,dep:59,status:"Not Started"},
  {fn:"Overall Launch Plan",sf:"Marketing Messages",task:"Regulatory approval for launch content - if any claims*",spoc:"Regulatory/Shrey",td:3,wd:2,dep:65,isOptional:true,status:"Not Started"},
  // 67-69 Insta Launch — correct order: halt → pre → post
  // IG Post-launch (idx 69): depEnd:76 → start = Going Live on D2C's start (same day), td:0
  // IG Pre-launch (idx 68): depEnd:69 → end = IG Post-launch start, back-calc 1 day
  // IG halt (idx 67): depEnd:68 → end = IG Pre-launch start, back-calc 1 day
  {fn:"Overall Launch Plan",sf:"Insta Launch",task:"IG halt in regular programing",spoc:"Media Labs",td:1,wd:1,dep:null,depEnd:68,status:"Not Started"},
  {fn:"Overall Launch Plan",sf:"Insta Launch",task:"IG Pre-launch/Teaser",spoc:"Media Labs",td:1,wd:1,dep:null,depEnd:69,status:"Not Started"},
  // IG Post-launch: depEnd:76 — its start+end = Going Live on D2C start (same day)
  // Stage 2 back-calc sets this at build time; cascadeAndCP depEnd pass keeps it live
  {fn:"Overall Launch Plan",sf:"Insta Launch",task:"IG Post-launch",spoc:"Media Labs",td:0,wd:0,dep:null,depEnd:76,status:"Not Started"},
  // 70-76 DTC Website
  {fn:"Overall Launch Plan",sf:"DTC Website",task:"Finalize Listing SKUs for D2C",spoc:"Shrey + Abhinav",td:3,wd:3,dep:59,status:"Not Started"},
  // Home Page banner: depEnd:72 → end = Figma Wireframe start; start = end - 30 days
  {fn:"Overall Launch Plan",sf:"DTC Website",task:"Home Page banner + Isolight page brief",spoc:"Ananya + Krishni",td:30,wd:20,dep:null,depEnd:72,status:"Not Started",remarks:"3 sub-brand pages"},
  // Figma Wireframe: depEnd:73 → end = Figma Final handover start; start = end - 30 days
  {fn:"Overall Launch Plan",sf:"DTC Website",task:"Figma design Wireframe - Product page + Shop Page",spoc:"D2C Team (Bhavesh)",td:30,wd:21,dep:null,depEnd:73,status:"Not Started"},
  // Figma Final handover: dep:61 (D2C listing images)
  {fn:"Overall Launch Plan",sf:"DTC Website",task:"Figma Final images handover",spoc:"D2C Team (Bhavesh)",td:7,wd:5,dep:61,status:"Not Started"},
  {fn:"Overall Launch Plan",sf:"DTC Website",task:"Figma and Listing Images Proof Read",spoc:"Abhinav",td:2,wd:2,dep:73,status:"Not Started"},
  {fn:"Overall Launch Plan",sf:"DTC Website",task:"Handover final figma to developers",spoc:"Abhinav",td:7,wd:5,dep:74,status:"Not Started"},
  // dep2:55 = Connect FG to forward warehouses (warehouse must be ready before go-live)
  {fn:"Overall Launch Plan",sf:"DTC Website",task:"Going Live on D2C",spoc:"Abhinav",td:0,wd:0,dep:75,dep2:55,status:"Not Started"},
  // 77-79 Amazon & Q-Com
  {fn:"Overall Launch Plan",sf:"Amazon",task:"Sharing Listing Images with Amazon",spoc:"Shrey",td:0,wd:0,dep:62,status:"Not Started"},
  {fn:"Overall Launch Plan",sf:"Amazon",task:"Dispatch first set of POs on Amazon",spoc:"Ankita",td:4,wd:2,dep:76,status:"Not Started"},
  {fn:"Overall Launch Plan",sf:"Q-Com",task:"Dispatch first set of POs on Q-Com",spoc:"KAMs",td:4,wd:2,dep:76,status:"Not Started"},
];

// ─── BUILD FROM TEMPLATE ─────────────────────────────────────────────────────
// dep    = forward dep: start = predecessor's effectiveEnd
// depEnd = backward: this row's END = row[depEnd]'s START; start = end - td calendar days
// depElse = fallback when primary dep is filtered out (New Project builder)
function buildFromTemplate(template, startDate) {
  const built = {};
  const rows = new Array(template.length).fill(null);

  // Stage 1: forward-dep rows (dep + optional dep2 for dual-predecessor rows)
  template.forEach((t, ti) => {
    if (t.depEnd != null) return;
    let start;
    if (t.dep == null) {
      start = startDate;
    } else {
      const depRow = built[t.dep];
      if (depRow) {
        start = getEffectiveEnd(depRow) || startDate;
      } else if (t.depElse != null) {
        const elseRow = built[t.depElse];
        start = elseRow ? (getEffectiveEnd(elseRow) || startDate) : startDate;
      } else {
        start = startDate;
      }
    }
    if (t.dep2 != null) {
      const dep2Row = built[t.dep2];
      if (dep2Row) {
        const dep2End = getEffectiveEnd(dep2Row) || startDate;
        if (dep2End > start) start = dep2End;
      }
    }
    const end = t.td > 0 ? addCalendarDays(start, t.td) : start;
    const row = {
      id:ti, fn:t.fn, sf:t.sf, task:t.task, spoc:t.spoc,
      start, end, revEnd:null,
      totalDays:t.td||0, workingDays:networkDays(start,end), delayDays:null,
      status:t.status||"Not Started", remarks:t.remarks||"",
      isCritical:false, isNearCritical:false, floatDays:null, isOptional:!!t.isOptional,
      dep:t.dep, depId:t.dep!=null?t.dep:null,
      dep2Id:t.dep2!=null?t.dep2:null,
      depElseId:t.depElse!=null?t.depElse:null,
      depEnd:t.depEnd||null,
    };
    rows[ti]=row; built[ti]=row;
  });

  // Stage 2: depEnd rows — up to 8 iterations for chained back-calc
  for (let iter=0; iter<8; iter++) {
    let changed=false;
    template.forEach((t,ti) => {
      if (t.depEnd==null) return;
      const anchor=built[t.depEnd];
      if (!anchor) return;
      const end=anchor.start; if (!end) return;
      const start = t.td>0 ? subtractCalendarDays(end,t.td) : end;
      const prev=rows[ti];
      if (prev && prev.start===start) return;
      const row={
        id:ti, fn:t.fn, sf:t.sf, task:t.task, spoc:t.spoc,
        start, end, revEnd:null,
        totalDays:t.td||0, workingDays:networkDays(start,end), delayDays:null,
        status:t.status||"Not Started", remarks:t.remarks||"",
        isCritical:false, isOptional:!!t.isOptional,
        dep:t.dep, depId:t.dep!=null?t.dep:null,
        dep2Id:t.dep2!=null?t.dep2:null,
        depElseId:t.depElse!=null?t.depElse:null,
        depEnd:t.depEnd,
      };
      rows[ti]=row; built[ti]=row; changed=true;
    });
    if (!changed) break;
  }

  const finalRows = rows.filter(r=>r!=null);
  // Compute dynamic CP + float on fresh build
  const { cpIds, nearCriticalIds, floatById, topoIds } = computeCriticalPath(finalRows);
  return finalRows.map(r=>({
    ...r,
    isCritical: cpIds.has(r.id),
    isNearCritical: nearCriticalIds.has(r.id),
    floatDays: floatById[r.id] != null ? floatById[r.id] : null,
    topoOrder: topoIds.indexOf(r.id),
  }));
}

// ─── Q2 FIX: BACK-CALCULATE FROM GO-LIVE (self-correcting) ──────────────────
// 1. Estimate project start by walking longest dep-chain backward
// 2. Build forward, measure actual go-live produced
// 3. Shift start by the gap and rebuild — repeat until go-live matches target
function buildFromTemplateBackward(template, targetGoLive) {
  // Walk dep chains backward from terminal nodes to find longest span
  const hasSuccessor = new Set();
  template.forEach(t => { if (t.dep!=null) hasSuccessor.add(t.dep); });
  const terminals = template.map((_,i)=>i).filter(i =>
    !hasSuccessor.has(i) && !template[i].depEnd
  );
  let maxSpan = 0;
  function walkBack(idx, accum, visited) {
    if (visited.has(idx)) return;
    visited.add(idx);
    const t = template[idx]; if (!t) return;
    const total = accum + (t.td||0);
    if (t.dep == null) { if (total > maxSpan) maxSpan = total; return; }
    walkBack(t.dep, total, visited);
  }
  terminals.forEach(ti => walkBack(ti, 0, new Set()));
  if (maxSpan === 0) maxSpan = template.filter(t=>!t.depEnd).reduce((s,t)=>s+(t.td||0),0);

  // First forward build
  let start = subtractCalendarDays(targetGoLive, maxSpan);
  let built = buildFromTemplate(template, start);

  // Helper: find actual go-live from built rows
  const actualGL = rows => {
    for (const name of ["Going Live on D2C","IG Post-launch"]) {
      const r = rows.find(x=>x.task===name); if (r&&r.end) return r.end;
    }
    const ends = rows.filter(r=>r.end).map(r=>r.end).sort();
    return ends[ends.length-1] || targetGoLive;
  };

  // Self-correct: shift start by the difference between actual and target go-live
  for (let i=0; i<4; i++) {
    const gl = actualGL(built);
    const diff = Math.round((new Date(targetGoLive)-new Date(gl))/86400000);
    if (diff === 0) break;
    start = addCalendarDays(start, diff);
    built = buildFromTemplate(template, start);
  }
  return built;
}

// ─── DEMO DATA ────────────────────────────────────────────────────────────────
const INITIAL_ROWS = buildFromTemplate(ISOLATE_TEMPLATE, "2026-01-29");

const EXCEL_OVERRIDES = {
  "Product Version 1":              {status:"Done",      start:"2026-01-29",end:"2026-02-05"},
  "Consumer Tastings 1":            {status:"Done",      start:"2026-02-05",end:"2026-02-10"},
  "Product Version 2":              {status:"Done",      start:"2026-02-10",end:"2026-02-17",revEnd:"2026-03-02"},
  "Consumer Tastings 2":            {status:"In-progress",start:"2026-03-02",end:"2026-03-17"},
  "Recipe Lock":                    {status:"Not Started",start:"2026-03-17",end:"2026-03-21"},
  "Lab tests (BOP + Label Mandate Sheet Finalize + Shelf Life test)":{status:"Not Started",start:"2026-03-21",end:"2026-04-20"},
  "Packaging Format":               {status:"Done",      start:"2026-01-29",end:"2026-02-02"},
  "SKU Mix":                        {status:"Done",      start:"2026-02-02",end:"2026-02-03"},
  "Consumer work - Functional Pro vs Lifestyle user":{status:"Done",start:"2026-02-13",end:"2026-03-10"},
  "Core proposition decision":      {status:"Done",      start:"2026-02-02",end:"2026-02-05"},
  "Shashank's feedback":            {status:"Done",      start:"2026-02-05",end:"2026-02-10"},
  "Brief to TOD":                   {status:"Done",      start:"2026-02-10",end:"2026-02-12",revEnd:"2026-02-17"},
  "V1 of Pouch Artwork":            {status:"Done",      start:"2026-02-17",end:"2026-02-24"},
  "Feedback from Category + Consumer work pov share":{status:"Done",start:"2026-02-24",end:"2026-02-25"},
  "V2 of Pouch Artwork":            {status:"Done",      start:"2026-02-25",end:"2026-03-04"},
  "Feedback from Shashank/Dhvanil": {status:"Done",      start:"2026-03-04",end:"2026-03-08"},
  "V3 of Pouch Artwork":            {status:"In-progress",start:"2026-03-08",end:"2026-03-15"},
  "Feedback from Shashank/Dhvanil (V3)":{status:"Not Started",start:"2026-03-15",end:"2026-03-19"},
};
const DEMO_ROWS = INITIAL_ROWS.map(r => {
  const ov = EXCEL_OVERRIDES[r.task]; if (!ov) return r;
  const nr = {...r,...ov};
  nr.workingDays = networkDays(nr.start, nr.end);
  nr.delayDays = nr.revEnd ? delayCalendarDays(nr.end, nr.revEnd) : null;
  return nr;
});

const MILESTONES = [
  {name:"Product Recipe Lock",   start:"2026-01-29",end:"2026-03-21"},
  {name:"Lab tests / BOP",       start:"2026-03-21",end:"2026-04-20"},
  {name:"Artwork Handover",      start:"2026-02-02",end:"2026-05-09"},
  {name:"Pouch Printing",        start:"2026-05-15",end:"2026-06-15"},
  {name:"BBK Stock Run",         start:"2026-06-19",end:"2026-06-22"},
  {name:"Warehouse Readiness",   start:"2026-06-22",end:"2026-06-29"},
  {name:"Launch",                start:"2026-07-03",end:"2026-07-03"},
  {name:"Channel PO Dispatch",   start:"2026-07-03",end:"2026-07-07"},
];
// ─── ICONS ────────────────────────────────────────────────────────────────────
const I = {
  Network:  ()=><svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2"><circle cx="12" cy="5" r="2"/><circle cx="5" cy="19" r="2"/><circle cx="19" cy="19" r="2"/><line x1="12" y1="7" x2="5" y2="17"/><line x1="12" y1="7" x2="19" y2="17"/></svg>,
  Gantt:    ()=><svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2"><rect x="3" y="4" width="18" height="3" rx="1"/><rect x="7" y="10" width="10" height="3" rx="1"/><rect x="3" y="16" width="14" height="3" rx="1"/></svg>,
  Board:    ()=><svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2"><rect x="3" y="3" width="7" height="7"/><rect x="14" y="3" width="7" height="7"/><rect x="14" y="14" width="7" height="7"/><rect x="3" y="14" width="7" height="7"/></svg>,
  Bell:     ()=><svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2"><path d="M18 8A6 6 0 0 0 6 8c0 7-3 9-3 9h18s-3-2-3-9"/><path d="M13.73 21a2 2 0 0 1-3.46 0"/></svg>,
  Plus:     ()=><svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2.5"><line x1="12" y1="5" x2="12" y2="19"/><line x1="5" y1="12" x2="19" y2="12"/></svg>,
  Trash:    ()=><svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2"><polyline points="3 6 5 6 21 6"/><path d="M19 6l-1 14H6L5 6"/><path d="M10 11v6"/><path d="M14 11v6"/><path d="M9 6V4h6v2"/></svg>,
  Upload:   ()=><svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><polyline points="17 8 12 3 7 8"/><line x1="12" y1="3" x2="12" y2="15"/></svg>,
  Download: ()=><svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><polyline points="7 10 12 15 17 10"/><line x1="12" y1="15" x2="12" y2="3"/></svg>,
  Mail:     ()=><svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2"><path d="M4 4h16c1.1 0 2 .9 2 2v12c0 1.1-.9 2-2 2H4c-1.1 0-2-.9-2-2V6c0-1.1.9-2 2-2z"/><polyline points="22,6 12,13 2,6"/></svg>,
  Copy:     ()=><svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2"><rect x="9" y="9" width="13" height="13" rx="2"/><path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"/></svg>,
  X:        ()=><svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2"><line x1="18" y1="6" x2="6" y2="18"/><line x1="6" y1="6" x2="18" y2="18"/></svg>,
  New:      ()=><svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2"><path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"/><polyline points="14 2 14 8 20 8"/><line x1="12" y1="18" x2="12" y2="12"/><line x1="9" y1="15" x2="15" y2="15"/></svg>,
  ChevD:    ()=><svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2"><polyline points="6 9 12 15 18 9"/></svg>,
  ChevR:    ()=><svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2"><polyline points="9 18 15 12 9 6"/></svg>,
  Zap:      ()=><svg width="11" height="11" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2.5"><polygon points="13 2 3 14 12 14 11 22 21 10 12 10 13 2"/></svg>,
};

// ─── EDITABLE CELL ────────────────────────────────────────────────────────────
function EC({value, type="text", onChange, opts=null, ro=false, style={}}) {
  const [ed, setEd] = useState(false);
  const [v, setV] = useState(value);
  const ref = useRef();
  useEffect(()=>{ setV(value); }, [value]);
  useEffect(()=>{ if(ed && ref.current) ref.current.focus(); }, [ed]);
  const commit = ()=>{ setEd(false); if(String(v)!==String(value)) onChange(v); };

  if (ro) return <div style={{padding:"2px 5px",fontSize:10,color:"#0369A1",background:"#EFF6FF",borderRadius:3,textAlign:"center",fontWeight:600,...style}}>{value??0}</div>;
  if (opts) return (
    <select value={value||""} onChange={e=>onChange(e.target.value)} style={{border:"none",background:"transparent",fontSize:10,cursor:"pointer",width:"100%",...style}}>
      {opts.map(o=><option key={o} value={o}>{o}</option>)}
    </select>
  );
  if (ed) return <input ref={ref} type={type} value={v||""} onChange={e=>setV(e.target.value)} onBlur={commit} onKeyDown={e=>{if(e.key==="Enter")commit();if(e.key==="Escape"){setV(value);setEd(false);}}} style={{border:"1px solid #3B82F6",borderRadius:3,padding:"2px 4px",fontSize:10,width:"100%",outline:"none",...style}}/>;
  return <div onClick={()=>setEd(true)} title="Click to edit" style={{cursor:"text",minHeight:18,padding:"2px 5px",borderRadius:3,fontSize:10,color:value?"#1F2937":"#D1D5DB",...style}}>{value||<span style={{opacity:.4,fontStyle:"italic"}}>—</span>}</div>;
}

// ─── ADD ROW MODAL ────────────────────────────────────────────────────────────
// FIX #11: add row to any section
function AddRowModal({groups, onAdd, onClose}) {
  const [fn, setFn] = useState(groups[0]?.fn||"");
  const [sf, setSf] = useState("");
  const [task, setTask] = useState("");
  const [spoc, setSpoc] = useState("");
  const [wd, setWd] = useState(1);
  const [afterId, setAfterId] = useState("");

  const fnGroups = groups.filter(g=>g.fn===fn);
  const targetGroup = fnGroups.find(g=>g.sf===sf) || fnGroups[0];

  useEffect(()=>{ if(fnGroups[0]) setSf(fnGroups[0].sf); }, [fn]);

  const save = () => {
    if (!task.trim()) return;
    const refRow = targetGroup?.rows.find(r=>String(r.id)===afterId) || targetGroup?.rows[targetGroup.rows.length-1];
    onAdd({ fn, sf: sf||"New Section", task, spoc, td: parseInt(wd)||1, afterId: refRow?.id });
    onClose();
  };

  return (
    <div style={{position:"fixed",inset:0,background:"rgba(0,0,0,.45)",zIndex:2000,display:"flex",alignItems:"center",justifyContent:"center"}}>
      <div style={{background:"#FFF",borderRadius:14,padding:24,width:480,boxShadow:"0 20px 50px rgba(0,0,0,.25)"}}>
        <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:18}}>
          <h3 style={{margin:0,fontSize:14,fontWeight:700,color:"#1B2A4A"}}>Add New Activity</h3>
          <button onClick={onClose} style={{background:"none",border:"none",cursor:"pointer",color:"#9CA3AF"}}><I.X/></button>
        </div>
        <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:10,marginBottom:12}}>
          <div>
            <label style={{fontSize:10,color:"#6B7280",display:"block",marginBottom:3}}>Function</label>
            <select value={fn} onChange={e=>setFn(e.target.value)} style={{width:"100%",padding:"7px 8px",border:"1px solid #E5E7EB",borderRadius:6,fontSize:11}}>
              {[...new Set(groups.map(g=>g.fn))].map(f=><option key={f}>{f}</option>)}
            </select>
          </div>
          <div>
            <label style={{fontSize:10,color:"#6B7280",display:"block",marginBottom:3}}>Sub-Function</label>
            <input value={sf} onChange={e=>setSf(e.target.value)} placeholder="Sub-function name" style={{width:"100%",padding:"7px 8px",border:"1px solid #E5E7EB",borderRadius:6,fontSize:11,boxSizing:"border-box"}}/>
          </div>
        </div>
        <div style={{marginBottom:10}}>
          <label style={{fontSize:10,color:"#6B7280",display:"block",marginBottom:3}}>Insert after activity</label>
          <select value={afterId} onChange={e=>setAfterId(e.target.value)} style={{width:"100%",padding:"7px 8px",border:"1px solid #E5E7EB",borderRadius:6,fontSize:11}}>
            <option value="">— End of section —</option>
            {(targetGroup?.rows||[]).map(r=><option key={r.id} value={r.id}>{r.task}</option>)}
          </select>
        </div>
        <div style={{marginBottom:10}}>
          <label style={{fontSize:10,color:"#6B7280",display:"block",marginBottom:3}}>Task Name *</label>
          <input value={task} onChange={e=>setTask(e.target.value)} placeholder="Enter activity name" style={{width:"100%",padding:"7px 8px",border:"1px solid #E5E7EB",borderRadius:6,fontSize:11,boxSizing:"border-box"}}/>
        </div>
        <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:10,marginBottom:16}}>
          <div>
            <label style={{fontSize:10,color:"#6B7280",display:"block",marginBottom:3}}>SPOC</label>
            <input value={spoc} onChange={e=>setSpoc(e.target.value)} style={{width:"100%",padding:"7px 8px",border:"1px solid #E5E7EB",borderRadius:6,fontSize:11,boxSizing:"border-box"}}/>
          </div>
          <div>
            <label style={{fontSize:10,color:"#6B7280",display:"block",marginBottom:3}}>Total Days (calendar)</label>
            <input type="number" min="0" value={wd} onChange={e=>setWd(e.target.value)} style={{width:"100%",padding:"7px 8px",border:"1px solid #E5E7EB",borderRadius:6,fontSize:11,boxSizing:"border-box"}}/>
          </div>
        </div>
        <div style={{display:"flex",gap:8}}>
          <button onClick={save} style={{flex:1,padding:"9px 0",background:"#1B2A4A",color:"#FFF",border:"none",borderRadius:7,cursor:"pointer",fontSize:12,fontWeight:700}}>Add Activity</button>
          <button onClick={onClose} style={{padding:"9px 16px",background:"#F3F4F6",border:"1px solid #E5E7EB",borderRadius:7,cursor:"pointer",fontSize:12}}>Cancel</button>
        </div>
      </div>
    </div>
  );
}

// ─── NEW PROJECT BUILDER (Path A) ─────────────────────────────────────────────
// FIX #12: back-calc mode actually works
const ALL_FUNCTIONS = Object.keys(FN_COLORS);

function NewProjectBuilder({onGenerate, onCancel}) {
  const [name, setName] = useState("New Launch");
  const [goLive, setGoLive] = useState("2026-07-03");
  const [mode, setMode] = useState("forward");
  const [startDate, setStartDate] = useState("2026-01-01");
  const [selFns, setSelFns] = useState(new Set(ALL_FUNCTIONS));
  const [expanded, setExpanded] = useState(new Set());
  // Activity selection: key = fn||sf||i -> checked bool
  const [checked, setChecked] = useState(()=>{
    const m={};
    ISOLATE_TEMPLATE.forEach((t,i)=>{ m[`${t.fn}||${t.sf}||${i}`] = !t.isOptional; });
    return m;
  });

  const toggleFn = fn => setSelFns(p=>{const n=new Set(p); n.has(fn)?n.delete(fn):n.add(fn); return n;});
  const toggleSF = k => setExpanded(p=>{const n=new Set(p); n.has(k)?n.delete(k):n.add(k); return n;});

  // Group template by fn->sf
  const grouped = useMemo(()=>{
    const g={};
    ISOLATE_TEMPLATE.forEach((t,i)=>{
      if(!g[t.fn]) g[t.fn]={};
      if(!g[t.fn][t.sf]) g[t.fn][t.sf]=[];
      g[t.fn][t.sf].push({...t, _i:i});
    });
    return g;
  },[]);

  const generate = () => {
    // Collect selected original indices
    const selectedOriginalIndices = ISOLATE_TEMPLATE.map((_,i)=>i).filter(i=>{
      const t = ISOLATE_TEMPLATE[i];
      return selFns.has(t.fn) && checked[`${t.fn}||${t.sf}||${i}`];
    });

    // Build old-index -> new-index map for dep remapping
    const oldToNew = {};
    selectedOriginalIndices.forEach((origIdx, newIdx) => { oldToNew[origIdx] = newIdx; });

    // Remap deps and depEnd; use depElse if primary dep filtered out
    const filteredTemplate = selectedOriginalIndices.map(origIdx => {
      const t = ISOLATE_TEMPLATE[origIdx];
      // Primary dep
      let newDep = null;
      if (t.dep != null) {
        if (oldToNew[t.dep] != null) {
          newDep = oldToNew[t.dep];
        } else if (t.depElse != null && oldToNew[t.depElse] != null) {
          // Primary dep filtered out — use fallback
          newDep = oldToNew[t.depElse];
        }
        // If both filtered out, dep stays null (becomes anchor)
      }
      const newDepEnd = (t.depEnd != null && oldToNew[t.depEnd] != null) ? oldToNew[t.depEnd] : null;
      // Also remap dep2 — without this, dual-predecessor rows (like Going Live on D2C)
      // lose their second predecessor when template is filtered
      const newDep2 = (t.dep2 != null && oldToNew[t.dep2] != null) ? oldToNew[t.dep2] : null;
      return {...t, dep: newDep, dep2: newDep2, depElse: undefined, depEnd: newDepEnd};
    });

    let rows;
    if (mode==="backward") {
      rows = buildFromTemplateBackward(filteredTemplate, goLive);
    } else {
      rows = buildFromTemplate(filteredTemplate, startDate);
    }
    // Reset all statuses to "Not Started" for a clean new network
    rows = rows.map(r => ({...r, status: "Not Started"}));
    onGenerate(rows, name);
  };

  return (
    <div style={{background:"#FFF",borderRadius:12,padding:24,maxWidth:800,margin:"0 auto",boxShadow:"0 4px 20px rgba(0,0,0,.1)"}}>
      <div style={{display:"flex",alignItems:"center",gap:10,marginBottom:20}}>
        <div style={{width:34,height:34,background:"#1B2A4A",borderRadius:8,display:"flex",alignItems:"center",justifyContent:"center"}}><I.New/></div>
        <div>
          <h2 style={{margin:0,fontSize:16,fontWeight:800,color:"#1B2A4A"}}>New Project — Build from Scratch</h2>
          <p style={{margin:0,fontSize:10,color:"#9CA3AF"}}>Select the functions you need, review activities, then generate your network</p>
        </div>
      </div>

      <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:12,marginBottom:16,padding:14,background:"#F8FAFC",borderRadius:8}}>
        <div>
          <label style={{fontSize:10,fontWeight:600,color:"#374151",display:"block",marginBottom:4}}>Project Name</label>
          <input value={name} onChange={e=>setName(e.target.value)} style={{width:"100%",padding:"7px 9px",border:"1px solid #E5E7EB",borderRadius:6,fontSize:11,boxSizing:"border-box"}}/>
        </div>
        <div>
          <label style={{fontSize:10,fontWeight:600,color:"#374151",display:"block",marginBottom:4}}>Go-Live Date</label>
          <input type="date" value={goLive} onChange={e=>setGoLive(e.target.value)} style={{width:"100%",padding:"7px 9px",border:"1px solid #E5E7EB",borderRadius:6,fontSize:11,boxSizing:"border-box"}}/>
        </div>
        <div>
          <label style={{fontSize:10,fontWeight:600,color:"#374151",display:"block",marginBottom:4}}>Planning Mode</label>
          <div style={{display:"flex",gap:6}}>
            {[["forward","▶ Forward from start"],["backward","◀ Back-calculate from go-live"]].map(([v,l])=>(
              <button key={v} onClick={()=>setMode(v)} style={{padding:"5px 10px",border:`1px solid ${mode===v?"#1B2A4A":"#E5E7EB"}`,borderRadius:6,cursor:"pointer",background:mode===v?"#1B2A4A":"#FFF",color:mode===v?"#FFF":"#374151",fontSize:10,fontWeight:mode===v?700:400}}>{l}</button>
            ))}
          </div>
        </div>
        {mode==="forward" && (
          <div>
            <label style={{fontSize:10,fontWeight:600,color:"#374151",display:"block",marginBottom:4}}>Project Start Date</label>
            <input type="date" value={startDate} onChange={e=>setStartDate(e.target.value)} style={{width:"100%",padding:"7px 9px",border:"1px solid #E5E7EB",borderRadius:6,fontSize:11,boxSizing:"border-box"}}/>
          </div>
        )}
        {mode==="backward" && (
          <div style={{padding:"8px",background:"#FFFBEB",borderRadius:6,border:"1px solid #FDE68A",fontSize:10,color:"#92400E"}}>
            ◀ Network will back-calculate from <strong>{goLive}</strong>. Start date is automatically derived from total WDs.
          </div>
        )}
      </div>

      {/* Function chips */}
      <div style={{marginBottom:12}}>
        <label style={{fontSize:10,fontWeight:700,color:"#374151",display:"block",marginBottom:6}}>Select Functions to Include</label>
        <div style={{display:"flex",flexWrap:"wrap",gap:6}}>
          {ALL_FUNCTIONS.map(fn=>{
            const fc=FN_COLORS[fn]||{bg:"#F3F4F6",border:"#9CA3AF",text:"#374151"};
            const sel=selFns.has(fn);
            return <button key={fn} onClick={()=>toggleFn(fn)} style={{padding:"5px 12px",borderRadius:20,border:`2px solid ${sel?fc.border:"#E5E7EB"}`,background:sel?fc.bg:"#F9FAFB",color:sel?fc.text:"#9CA3AF",fontSize:10,fontWeight:sel?700:400,cursor:"pointer",transition:"all .15s"}}>{sel?"✓ ":""}{fn}</button>;
          })}
        </div>
      </div>

      {/* Accordions */}
      <div style={{marginBottom:16,maxHeight:340,overflowY:"auto",border:"1px solid #E5E7EB",borderRadius:8}}>
        {ALL_FUNCTIONS.filter(fn=>selFns.has(fn)).map(fn=>{
          const fc=FN_COLORS[fn]||{bg:"#F3F4F6",border:"#9CA3AF",text:"#374151"};
          const sfs = grouped[fn]||{};
          return (
            <div key={fn}>
              <div style={{background:fc.bg,borderBottom:`1px solid ${fc.border}30`,padding:"7px 12px"}}>
                <span style={{fontSize:11,fontWeight:800,color:fc.text}}>{fn}</span>
              </div>
              {Object.entries(sfs).map(([sf,acts])=>{
                const k=`${fn}||${sf}`;
                const open=expanded.has(k);
                const selCount=acts.filter(a=>checked[`${a.fn}||${a.sf}||${a._i}`]).length;
                return (
                  <div key={sf}>
                    <button onClick={()=>toggleSF(k)} style={{width:"100%",display:"flex",alignItems:"center",justifyContent:"space-between",padding:"6px 14px 6px 20px",background:"#FAFAFA",border:"none",borderBottom:"1px solid #F3F4F6",cursor:"pointer",textAlign:"left"}}>
                      <span style={{fontSize:11,fontWeight:600,color:"#374151",display:"flex",alignItems:"center",gap:5}}>{open?<I.ChevD/>:<I.ChevR/>} {sf}</span>
                      <span style={{fontSize:9,color:"#9CA3AF"}}>{selCount}/{acts.length}</span>
                    </button>
                    {open && acts.map((a)=>{
                      const k2=`${a.fn}||${a.sf}||${a._i}`;
                      return (
                        <label key={a._i} style={{display:"flex",alignItems:"center",gap:8,padding:"5px 14px 5px 30px",borderBottom:"1px solid #F9FAFB",cursor:"pointer"}}>
                          <input type="checkbox" checked={!!checked[k2]} onChange={()=>setChecked(p=>({...p,[k2]:!p[k2]}))} style={{accentColor:"#1B2A4A",width:13,height:13}}/>
                          <span style={{flex:1,fontSize:10,color:checked[k2]?"#374151":"#D1D5DB"}}>{a.task}</span>
                          {a.isOptional&&<span style={{fontSize:8,background:"#FEF3C7",color:"#D97706",padding:"1px 5px",borderRadius:8,fontWeight:700}}>Optional</span>}
                          <span style={{fontSize:9,color:"#9CA3AF",minWidth:35,textAlign:"right"}}>{a.wd}WD</span>
                          <span style={{fontSize:9,color:"#6B7280",minWidth:70,textAlign:"right"}}>{a.spoc}</span>
                        </label>
                      );
                    })}
                  </div>
                );
              })}
            </div>
          );
        })}
      </div>

      <div style={{display:"flex",gap:10}}>
        <button onClick={generate} style={{flex:1,padding:"10px 0",background:"#1B2A4A",color:"#FFF",border:"none",borderRadius:8,cursor:"pointer",fontSize:13,fontWeight:700}}>⚡ Generate Network</button>
        <button onClick={onCancel} style={{padding:"10px 18px",background:"#F3F4F6",border:"1px solid #E5E7EB",borderRadius:8,cursor:"pointer",fontSize:13}}>Cancel</button>
      </div>
    </div>
  );
}

// ─── NETWORK TABLE ────────────────────────────────────────────────────────────
function NetworkTable({rows, onUpdate, onDelete, onAddRow, projectName, goLiveDate}) {
  const [showAddModal, setShowAddModal] = useState(false);

  const grouped = useMemo(()=>{
    const g={};
    rows.forEach(r=>{
      const k=`${r.fn}||${r.sf}`;
      if(!g[k]) g[k]={fn:r.fn,sf:r.sf,rows:[]};
      g[k].rows.push(r);
    });
    return Object.values(g);
  },[rows]);

  // FIX #3,4,7: update cascades downstream
  const updateRow = (id, field, value) => {
    const row = rows.find(r=>r.id===id);
    if (!row) return;
    let updated = {...row, [field]: value};

    if (field==="start" || field==="end") {
      updated.totalDays = calDays(updated.start, updated.end);
      updated.workingDays = networkDays(updated.start, updated.end);
    } else if (field==="totalDays") {
      const days = parseInt(value)||0;
      updated.end = addCalendarDays(updated.start, days);
      updated.workingDays = networkDays(updated.start, updated.end);
    }

    if (field==="revEnd" || field==="end" || field==="totalDays") {
      updated.delayDays = (updated.revEnd && updated.revEnd > updated.end)
        ? delayCalendarDays(updated.end, updated.revEnd) : null;
    }

    onUpdate(id, updated, true); // true = cascade
  };

  const exportCSV = () => {
    const h=["Function","Sub-Function","Task","Team SPOC","Start Date","End Date","Revised End Date","Total Days","Working Days","Delay Days","Status","Remarks"];
    const r2=rows.map(r=>[r.fn,r.sf,r.task,r.spoc,r.start,r.end,r.revEnd||"",r.totalDays,r.workingDays,r.delayDays??"-",r.status,r.remarks].map(v=>`"${String(v||"").replace(/"/g,'""')}"`).join(","));
    const csv=[h.join(","),...r2].join("\n");
    const a=document.createElement("a"); a.href="data:text/csv;charset=utf-8,"+encodeURIComponent(csv); a.download=`${projectName||"network"}.csv`; a.click();
  };

  const cs={padding:"4px 6px",fontSize:10,borderRight:"1px solid #F3F4F6",verticalAlign:"middle"};
  const th={...cs,background:"#1B2A4A",color:"#CBD5E1",fontWeight:700,textAlign:"left",position:"sticky",top:0,zIndex:2,fontSize:9};

  return (
    <div>
      <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:8}}>
        <span style={{fontSize:10,color:"#9CA3AF"}}>
          ⚡ = critical path &nbsp;|&nbsp; <span style={{color:"#0369A1"}}>Working Days</span> = NETWORKDAYS formula (auto) &nbsp;|&nbsp; Total Days = editable
        </span>
        <div style={{display:"flex",gap:7}}>
          <button onClick={()=>setShowAddModal(true)} style={{display:"flex",alignItems:"center",gap:5,padding:"6px 12px",background:"#EEF2FF",border:"1px dashed #6366F1",borderRadius:6,cursor:"pointer",fontSize:10,color:"#4F46E5",fontWeight:600}}>
            <I.Plus/> Add Activity
          </button>
          <button onClick={exportCSV} style={{display:"flex",alignItems:"center",gap:5,padding:"6px 12px",background:"#F3F4F6",border:"1px solid #E5E7EB",borderRadius:6,cursor:"pointer",fontSize:10,color:"#374151"}}>
            <I.Download/> Export CSV
          </button>
        </div>
      </div>

      <div style={{overflowX:"auto",borderRadius:8,border:"1px solid #E5E7EB",boxShadow:"0 1px 3px rgba(0,0,0,.05)"}}>
        <table style={{width:"100%",borderCollapse:"collapse",tableLayout:"fixed",minWidth:1080}}>
          <colgroup>
            <col style={{width:100}}/><col style={{width:92}}/><col style={{width:210}}/>
            <col style={{width:100}}/><col style={{width:84}}/><col style={{width:84}}/>
            <col style={{width:84}}/><col style={{width:58}}/><col style={{width:66}}/>
            <col style={{width:54}}/><col style={{width:88}}/><col style={{width:120}}/><col style={{width:34}}/>
          </colgroup>
          <thead>
            <tr>
              {["Function","Sub-Fn","Task","SPOC","Start Date","End Date","Revised End","Total Days","WD (formula)","Delay","Status","Remarks",""].map((h,i)=>
                <th key={i} style={th}>{h}</th>
              )}
            </tr>
          </thead>
          <tbody>
            {grouped.map(group=>{
              const fc=FN_COLORS[group.fn]||{bg:"#F9FAFB",border:"#E5E7EB",text:"#374151"};
              return group.rows.map((row,ri)=>{
                const sc=ST_COLORS[row.status]||ST_COLORS["Not Started"];
                const bg=row.isCritical?"#FFF8F8":(ri%2===0?"#FFF":"#FAFAFA");
                return (
                  <tr key={row.id} style={{background:bg,borderBottom:"1px solid #F3F4F6"}}>
                    {ri===0&&<td rowSpan={group.rows.length} style={{...cs,background:fc.bg,borderLeft:`3px solid ${fc.border}`,verticalAlign:"top",paddingTop:7}}><span style={{fontSize:9,fontWeight:800,color:fc.text}}>{group.fn}</span></td>}
                    {ri===0&&<td rowSpan={group.rows.length} style={{...cs,background:fc.bg,verticalAlign:"top",paddingTop:7,fontSize:9,color:fc.text}}>{group.sf}</td>}
                    <td style={cs}>
                      <div style={{display:"flex",alignItems:"center",gap:3}}>
                        {row.isCritical&&<span style={{color:"#EF4444",flexShrink:0}}><I.Zap/></span>}
                        {row.isNearCritical&&!row.isCritical&&(
                          <span title={"Near-critical: "+row.floatDays+"d float"}
                            style={{color:"#D97706",flexShrink:0,fontSize:9,fontWeight:700,lineHeight:1}}>!</span>
                        )}
                        <EC value={row.task} onChange={v=>updateRow(row.id,"task",v)} style={{flex:1}}/>
                      </div>
                    </td>
                    <td style={cs}><EC value={row.spoc} onChange={v=>updateRow(row.id,"spoc",v)}/></td>
                    <td style={cs}><EC value={row.start} type="date" onChange={v=>updateRow(row.id,"start",v)}/></td>
                    <td style={cs}><EC value={row.end} type="date" onChange={v=>updateRow(row.id,"end",v)}/></td>
                    <td style={cs}>
                      <EC value={row.revEnd||""} type="date" onChange={v=>updateRow(row.id,"revEnd",v||null)}
                        style={{color: row.revEnd?"#DC2626":"#9CA3AF"}}/>
                    </td>
                    <td style={cs}><EC value={row.totalDays??0} type="number" onChange={v=>updateRow(row.id,"totalDays",v)} style={{textAlign:"center"}}/></td>
                    <td style={cs}><EC value={row.workingDays??0} ro={true}/></td>
                    <td style={{...cs,textAlign:"center",color:row.delayDays>0?"#EF4444":"#9CA3AF",fontWeight:row.delayDays>0?700:400,fontSize:10}}>
                      {row.delayDays>0?`+${row.delayDays}d`:"—"}
                    </td>
                    <td style={cs}>
                      <EC value={row.status} opts={["Done","In-progress","Not Started","Delayed"]} onChange={v=>updateRow(row.id,"status",v)}
                        style={{background:sc.bg,color:sc.text,borderRadius:10,padding:"2px 6px",fontWeight:700,fontSize:9}}/>
                    </td>
                    <td style={cs}><EC value={row.remarks} onChange={v=>updateRow(row.id,"remarks",v)} style={{fontSize:9,color:"#9CA3AF"}}/></td>
                    <td style={{...cs,textAlign:"center",padding:2}}>
                      <button onClick={()=>onDelete(row.id)} style={{background:"none",border:"none",cursor:"pointer",color:"#EF4444",opacity:.6,padding:3,display:"flex"}}><I.Trash/></button>
                    </td>
                  </tr>
                );
              });
            })}
          </tbody>
        </table>
      </div>

      {showAddModal && <AddRowModal groups={grouped} onAdd={onAddRow} onClose={()=>setShowAddModal(false)}/>}
    </div>
  );
}

// ─── SUMMARY BAR ─────────────────────────────────────────────────────────────
function SummaryBar({rows, goLiveDate}) {
  const total=rows.length, done=rows.filter(r=>r.status==="Done").length;
  const inProg=rows.filter(r=>r.status==="In-progress").length;
  const delayed=rows.filter(r=>r.status==="Delayed"||r.delayDays>0).length;
  const pct=total?Math.round((done/total)*100):0;
  // FIX #2: dynamic days-to-go-live from actual goLiveDate
  const daysToGL = goLiveDate
    ? Math.ceil((new Date(goLiveDate)-new Date(todayStr()))/86400000)
    : 0;
  return (
    <div style={{display:"flex",gap:9,marginBottom:16,flexWrap:"wrap"}}>
      {[
        {label:"Total Activities",value:total,color:"#1B2A4A"},
        {label:"Done",value:done,color:"#059669"},
        {label:"In Progress",value:inProg,color:"#D97706"},
        {label:"Delayed",value:delayed,color:"#DC2626"},
        {label:"% Complete",value:`${pct}%`,color:"#6366F1"},
        {label:"Days to Go-Live",value:daysToGL>0?daysToGL:"—",color:"#0284C7"},
      ].map((c,i)=>(
        <div key={i} style={{background:"#FFF",border:"1px solid #E5E7EB",borderRadius:9,padding:"9px 16px",flex:"1 1 100px",boxShadow:"0 1px 2px rgba(0,0,0,.04)"}}>
          <div style={{fontSize:20,fontWeight:800,color:c.color}}>{c.value}</div>
          <div style={{fontSize:9,color:"#9CA3AF",marginTop:2}}>{c.label}</div>
        </div>
      ))}
    </div>
  );
}

// ─── GANTT CHART ─────────────────────────────────────────────────────────────
function GanttChart({rows, goLiveDate}) {
  const allDates = rows.filter(r=>r.start&&r.end).flatMap(r=>[new Date(r.start),new Date(r.end)]);
  if (!allDates.length) return <div style={{color:"#9CA3AF",padding:20}}>No data to display.</div>;
  const startDate = new Date(Math.min(...allDates));
  const endDate = goLiveDate ? new Date(Math.max(new Date(goLiveDate), new Date(Math.max(...allDates)))) : new Date(Math.max(...allDates));
  startDate.setDate(startDate.getDate()-3);
  endDate.setDate(endDate.getDate()+5);
  const span = endDate-startDate;
  const todayD = new Date(todayStr());
  const todayPct = Math.max(0,Math.min(100,((todayD-startDate)/span)*100));

  const months=[];
  let cur=new Date(startDate.getFullYear(),startDate.getMonth(),1);
  while(cur<=endDate){ months.push({label:cur.toLocaleDateString("en-IN",{month:"short",year:"2-digit"}),date:new Date(cur)}); cur=new Date(cur.getFullYear(),cur.getMonth()+1,1); }

  const validRows=rows.filter(r=>r.start&&r.end);
  return (
    <div style={{overflowX:"auto"}}>
      <div style={{minWidth:900}}>
        <div style={{display:"flex",borderBottom:"1px solid #E5E7EB",marginBottom:2}}>
          <div style={{width:280,minWidth:280,fontSize:9,color:"#6B7280",padding:"3px 7px",borderRight:"1px solid #E5E7EB"}}>Task</div>
          <div style={{flex:1,position:"relative",height:26}}>
            {months.map((m,i)=>{const p=((m.date-startDate)/span)*100; return <span key={i} style={{position:"absolute",left:`${p}%`,fontSize:8,color:"#9CA3AF",top:7,whiteSpace:"nowrap"}}>{m.label}</span>;})}
            <div style={{position:"absolute",left:`${todayPct}%`,top:0,bottom:0,width:2,background:"#F59E0B"}}/>
          </div>
        </div>
        <div style={{maxHeight:480,overflowY:"auto"}}>
          {validRows.map(row=>{
            const s=new Date(row.start),e=new Date(row.end);
            const left=Math.max(0,((s-startDate)/span)*100);
            const width=Math.max(0.3,((e-s)/span)*100);
            const fc=FN_COLORS[row.fn]||{border:"#6B7280"};
            const barColor=row.isCritical?"#EF4444":fc.border;
            return (
              <div key={row.id} style={{display:"flex",alignItems:"center",borderBottom:"1px solid #F9FAFB",height:28}}>
                <div style={{width:280,minWidth:280,padding:"0 7px",borderRight:"1px solid #F3F4F6",overflow:"hidden"}}>
                  <div style={{display:"flex",alignItems:"center",gap:3}}>
                    {row.isCritical&&<span style={{color:"#EF4444",fontSize:8}}>⚡</span>}
                    <span style={{fontSize:9,color:"#374151",whiteSpace:"nowrap",overflow:"hidden",textOverflow:"ellipsis"}}>{row.task}</span>
                  </div>
                  <span style={{fontSize:8,color:"#9CA3AF"}}>{row.spoc}</span>
                </div>
                <div style={{flex:1,position:"relative",height:"100%"}}>
                  <div style={{position:"absolute",left:`${todayPct}%`,top:0,bottom:0,width:1,background:"#FCD34D",opacity:.6}}/>
                  <div title={`${row.task} | ${row.start}→${row.end} | ${row.workingDays}WD | ${row.status}`}
                    style={{position:"absolute",left:`${left}%`,width:`${width}%`,top:"22%",height:"56%",background:barColor,borderRadius:3,opacity:row.status==="Done"?.55:.9,cursor:"pointer",minWidth:3}}/>
                  {row.revEnd&&row.revEnd>row.end&&(
                    <div style={{position:"absolute",left:`${Math.max(0,((new Date(row.end)-startDate)/span)*100)}%`,width:`${Math.max(.3,((new Date(row.revEnd)-new Date(row.end))/span)*100)}%`,top:"22%",height:"56%",background:"#EF4444",opacity:.35,borderRadius:"0 3px 3px 0",minWidth:2}}/>
                  )}
                </div>
              </div>
            );
          })}
        </div>
        <div style={{display:"flex",gap:14,padding:"8px 7px",borderTop:"1px solid #E5E7EB",fontSize:9,color:"#6B7280"}}>
          <span><span style={{display:"inline-block",width:10,height:7,background:"#EF4444",borderRadius:2,marginRight:4}}/>Critical Path</span>
          <span><span style={{display:"inline-block",width:1,height:12,background:"#F59E0B",marginRight:4}}/>Today</span>
          <span><span style={{display:"inline-block",width:10,height:7,background:"#EF4444",opacity:.35,borderRadius:2,marginRight:4}}/>Delay slip</span>
        </div>
      </div>
    </div>
  );
}

// ─── CRITICAL PATH FLOWCHART ──────────────────────────────────────────────────
function CPFlowchart({rows}) {
  const cpChain = useMemo(() => {
    return rows.filter(r => r.isCritical && r.start)
               .sort((a,b) => {
                 // Sort by topological order if available (gives correct logical sequence)
                 // Fall back to start date for robustness
                 const ta = a.topoOrder != null ? a.topoOrder : 9999;
                 const tb = b.topoOrder != null ? b.topoOrder : 9999;
                 if (ta !== tb) return ta - tb;
                 return (a.start||"") > (b.start||"") ? 1 : -1;
               });
  }, [rows]);

  const nonCp = useMemo(() =>
    rows.filter(r => !r.isCritical && r.start && r.end), [rows]);

  // Assign each non-CP row to the CP column it overlaps most in time
  function assignToCpNode(row) {
    if (!cpChain.length) return 0;
    let best = 0, bestOverlap = -Infinity;
    cpChain.forEach((cp, i) => {
      const rS = new Date(row.start), rE = new Date(row.end||row.start);
      const cS = new Date(cp.start), cE = new Date(cp.end||cp.start);
      const ov = Math.min(+rE,+cE) - Math.max(+rS,+cS);
      if (ov > bestOverlap) { bestOverlap = ov; best = i; }
    });
    return best;
  }

  const laneAbove = {}, laneBelow = {};
  nonCp.forEach(r => {
    const ci = assignToCpNode(r);
    if (!laneAbove[ci]) laneAbove[ci] = [];
    if (!laneBelow[ci]) laneBelow[ci] = [];
    if (laneAbove[ci].length <= laneBelow[ci].length) laneAbove[ci].push(r);
    else laneBelow[ci].push(r);
  });

  // Layout constants
  const NW=158, NH=70, PNH=58, HGAP=40, VCAP=14, PVGAP=8;
  const MAX_ABOVE=2, MAX_BELOW=2;
  const aboveH = MAX_ABOVE*(PNH+PVGAP);
  const belowH  = MAX_BELOW*(PNH+PVGAP);
  const ANCHOR_W=56;
  const startX=16;
  const firstCpX = startX+ANCHOR_W+HGAP;
  function cpX(i) { return firstCpX + i*(NW+HGAP); }
  const lastCpX = cpX(cpChain.length-1);
  const endX = lastCpX+NW+HGAP;
  const SVG_W = Math.max(900, endX+ANCHOR_W+24);
  const CY = aboveH+VCAP+16;
  const SVG_H = CY+NH+VCAP+belowH+40;
  const midCpY = CY+NH/2;
  const ANCHOR_H=44;
  const anchorY = CY+(NH-ANCHOR_H)/2;

  if (!cpChain.length) return (
    <div style={{padding:32,textAlign:"center",color:"#9CA3AF",fontSize:13}}>
      No critical path found. Generate or upload a network to compute it.
    </div>
  );

  function tr(s, n) { return s && s.length>n ? s.slice(0,n)+"..." : (s||""); }

  function cpColor(r) {
    if (r.status==="Done")        return {fill:"#D1FAE5",stroke:"#059669",text:"#065F46",chip:"#059669",chipTxt:"Done"};
    if (r.status==="In-progress") return {fill:"#FEF9C3",stroke:"#D97706",text:"#92400E",chip:"#D97706",chipTxt:"In Prog"};
    return {fill:"#FEE2E2",stroke:"#EF4444",text:"#991B1B",chip:"#6B7280",chipTxt:"Not Strt"};
  }

  function parColor(r) {
    if (r.status==="Done") return {fill:"#D1FAE5",stroke:"#059669",text:"#065F46"};
    if (r.isNearCritical)  return {fill:"#FEF3C7",stroke:"#D97706",text:"#92400E"};
    const fc = FN_COLORS[r.fn]||{bg:"#EFF6FF",border:"#3B82F6",text:"#1D4ED8"};
    return {fill:fc.bg, stroke:fc.border, text:fc.text};
  }

  // Render a parallel node — called as a function, not a JSX component
  function renderParNode(r, x, y, isAbove) {
    const c = parColor(r);
    const connX = x+NW/2;
    const connY1 = isAbove ? y+PNH : y;
    const connY2 = isAbove ? CY : CY+NH;
    const nearCrit = !!r.isNearCritical;
    return (
      <g key={"par"+r.id}>
        <line x1={connX} y1={connY1} x2={cpX(assignToCpNode(r))+NW/2} y2={connY2}
          stroke="#94A3B8" strokeWidth="1.5" strokeDasharray="5,3"
          markerEnd="url(#gray-arrow)"/>
        <rect x={x} y={y} width={NW} height={PNH} rx="5"
          fill={c.fill} stroke={c.stroke} strokeWidth={nearCrit ? 2.5 : 1.5}/>
        {nearCrit && (
          <text x={x+NW-12} y={y+12} fontSize="10" fill="#D97706"
            fontWeight="900" style={{fontFamily:"system-ui"}}>!</text>
        )}
        <text x={x+5} y={y+13} fontSize="8" fontWeight="700"
          fill={c.text} style={{fontFamily:"system-ui"}}>{tr(r.task,22)}</text>
        <text x={x+5} y={y+24} fontSize="7.5" fill={c.text}
          opacity=".8" style={{fontFamily:"system-ui"}}>{tr(r.spoc,20)}</text>
        <text x={x+5} y={y+35} fontSize="7.5" fill={c.stroke}
          fontWeight="600" style={{fontFamily:"system-ui"}}>
          {"("+r.totalDays+"d) "+r.start.slice(5)+" to "+(r.end?r.end.slice(5):"")}
        </text>
        {nearCrit && r.floatDays!=null && (
          <text x={x+5} y={y+46} fontSize="7" fill="#D97706"
            fontWeight="600" style={{fontFamily:"system-ui"}}>
            {"! float: "+r.floatDays+"d"}
          </text>
        )}
        <rect x={x+NW-54} y={y+PNH-16} width={50} height={13} rx="6"
          fill={c.stroke}/>
        <text x={x+NW-29} y={y+PNH-6} fontSize="7" fill="#FFF"
          textAnchor="middle" fontWeight="700" style={{fontFamily:"system-ui"}}>
          {r.status==="Done"?"Done":r.status==="In-progress"?"In Prog":"Not Strt"}
        </text>
      </g>
    );
  }

  return (
    <div style={{overflowX:"auto",overflowY:"auto",border:"1px solid #E5E7EB",borderRadius:10,background:"#F8FAFC"}}>
      {/* Legend */}
      <div style={{padding:"8px 14px 5px",borderBottom:"1px solid #F0F0F0",display:"flex",gap:16,alignItems:"center",flexWrap:"wrap"}}>
        <span style={{fontSize:11,fontWeight:700,color:"#1B2A4A"}}>Critical Path - auto-computed longest chain</span>
        <div style={{display:"flex",gap:12,fontSize:10,color:"#6B7280",flexWrap:"wrap"}}>
          {[
            {bg:"#FEE2E2",border:"2px solid #EF4444",label:"Critical path"},
            {bg:"#FEF3C7",border:"2.5px solid #D97706",label:"Near-critical (<=14d float)"},
            {bg:"#DBEAFE",border:"1.5px solid #3B82F6",label:"Parallel activity"},
            {bg:"#D1FAE5",border:"1.5px solid #059669",label:"Done"},
          ].map((it,i)=>(
            <span key={i} style={{display:"flex",alignItems:"center",gap:4}}>
              <span style={{display:"inline-block",width:14,height:10,background:it.bg,
                border:it.border,borderRadius:2}}/>
              {it.label}
            </span>
          ))}
        </div>
      </div>

      <svg width={SVG_W} height={SVG_H} style={{display:"block",minWidth:SVG_W}}>
        <defs>
          <marker id="red-arrow" markerWidth="8" markerHeight="8"
            refX="6" refY="4" orient="auto">
            <polygon points="0,0 8,4 0,8" fill="#EF4444"/>
          </marker>
          <marker id="gray-arrow" markerWidth="7" markerHeight="7"
            refX="5" refY="3.5" orient="auto">
            <polygon points="0,0 7,3.5 0,7" fill="#94A3B8"/>
          </marker>
        </defs>

        {/* Start anchor */}
        <rect x={startX} y={anchorY} width={ANCHOR_W} height={ANCHOR_H}
          rx="8" fill="#1B2A4A"/>
        <text x={startX+ANCHOR_W/2} y={anchorY+ANCHOR_H/2+4}
          textAnchor="middle" fontSize="11" fontWeight="800"
          fill="#FFF" style={{fontFamily:"system-ui"}}>Start</text>

        {/* Start to first CP arrow */}
        <line x1={startX+ANCHOR_W} y1={midCpY} x2={firstCpX-8} y2={midCpY}
          stroke="#EF4444" strokeWidth="2.5" markerEnd="url(#red-arrow)"/>

        {/* CP chain arrows */}
        {cpChain.map((r,i) => {
          if (i===cpChain.length-1) return null;
          return (
            <line key={"ca"+i}
              x1={cpX(i)+NW} y1={midCpY}
              x2={cpX(i+1)-8} y2={midCpY}
              stroke="#EF4444" strokeWidth="2.5"
              markerEnd="url(#red-arrow)"/>
          );
        })}

        {/* Last CP to End arrow */}
        <line x1={lastCpX+NW} y1={midCpY} x2={endX-8} y2={midCpY}
          stroke="#EF4444" strokeWidth="2.5" markerEnd="url(#red-arrow)"/>

        {/* End anchor */}
        <rect x={endX} y={anchorY} width={ANCHOR_W} height={ANCHOR_H}
          rx="8" fill="#1B2A4A"/>
        <text x={endX+ANCHOR_W/2} y={anchorY+ANCHOR_H/2+4}
          textAnchor="middle" fontSize="11" fontWeight="800"
          fill="#FFF" style={{fontFamily:"system-ui"}}>End</text>

        {/* CP nodes */}
        {cpChain.map((r,i) => {
          const x=cpX(i), y=CY;
          const c=cpColor(r);
          const isGL = r.task.toLowerCase().includes("going live");
          return (
            <g key={"cp"+r.id}>
              <rect x={x} y={y} width={NW} height={NH} rx="6"
                fill={isGL?"#FEF08A":c.fill}
                stroke={isGL?"#D97706":c.stroke}
                strokeWidth="2.5"/>
              <text x={x+4} y={y-4} fontSize="7.5" fill="#6B7280"
                style={{fontFamily:"system-ui"}}>
                {(r.start||"").slice(5)+" to "+(r.end||"").slice(5)}
              </text>
              <text x={x+5} y={y+16} fontSize="8.5" fontWeight="800"
                fill={isGL?"#92400E":c.text}
                style={{fontFamily:"system-ui"}}>
                {tr(r.task,21)}
              </text>
              {r.task.length>21 && (
                <text x={x+5} y={y+27} fontSize="8"
                  fill={isGL?"#92400E":c.text}
                  style={{fontFamily:"system-ui"}}>
                  {tr(r.task.slice(21),22)}
                </text>
              )}
              <text x={x+5} y={y+40} fontSize="8"
                fill={isGL?"#D97706":c.stroke}
                fontWeight="600" style={{fontFamily:"system-ui"}}>
                {"("+r.totalDays+" days)"}
              </text>
              <text x={x+5} y={y+52} fontSize="7.5"
                fill={isGL?"#92400E":c.text}
                opacity=".8" style={{fontFamily:"system-ui"}}>
                {tr(r.spoc,23)}
              </text>
              <rect x={x+NW-54} y={y+NH-17} width={50} height={13}
                rx="6" fill={c.chip}/>
              <text x={x+NW-29} y={y+NH-7} fontSize="7.5" fill="#FFF"
                textAnchor="middle" fontWeight="700"
                style={{fontFamily:"system-ui"}}>
                {c.chipTxt}
              </text>
            </g>
          );
        })}

        {/* Parallel nodes above */}
        {cpChain.map((_,ci) => {
          return (laneAbove[ci]||[]).slice(0,MAX_ABOVE).map((r,pi) => {
            const x = cpX(ci);
            const y = CY - VCAP - (pi+1)*(PNH+PVGAP) - 4;
            return renderParNode(r, x, y, true);
          });
        })}

        {/* Parallel nodes below */}
        {cpChain.map((_,ci) => {
          return (laneBelow[ci]||[]).slice(0,MAX_BELOW).map((r,pi) => {
            const x = cpX(ci);
            const y = CY + NH + VCAP + pi*(PNH+PVGAP) + 4;
            return renderParNode(r, x, y, false);
          });
        })}
      </svg>
    </div>
  );
}

// ─── DASHBOARD MODULE ─────────────────────────────────────────────────────────
function DashboardModule({rows, goLiveDate}) {
  const todayD = new Date(todayStr());
  const goLive = goLiveDate ? new Date(goLiveDate) : new Date("2026-07-03");
  // FIX #9: dynamic days to go-live
  const daysToGL = Math.ceil((goLive-todayD)/86400000);
  const total=rows.length, done=rows.filter(r=>r.status==="Done").length;
  const delayed=rows.filter(r=>r.status==="Delayed"||r.delayDays>0).length;
  const pct=total?Math.round((done/total)*100):0;

  const getPhase = (start,end)=>{
    const pr=rows.filter(r=>{if(!r.start||!r.end)return false; return new Date(r.start)>=new Date(start)&&new Date(r.end)<=new Date(end);});
    if(!pr.length) return {pct:0,status:"amber"};
    const d=pr.filter(r=>r.status==="Done").length;
    const del=pr.filter(r=>r.status==="Delayed"||r.delayDays>0).length;
    const p=Math.round((d/pr.length)*100);
    return {pct:p,status:del>0?"red":p===100?"green":"amber"};
  };
  const rag={green:"#059669",amber:"#D97706",red:"#DC2626"};
  const spocMap={};
  rows.forEach(r=>{ if(!r.spoc)return; r.spoc.split("/").forEach(s=>{ const sp=s.trim(); if(!spocMap[sp])spocMap[sp]=[]; spocMap[sp].push(r); }); });

  return (
    <div>
      <div style={{display:"grid",gridTemplateColumns:"repeat(4,1fr)",gap:12,marginBottom:18}}>
        {[
          {label:"Days to Go-Live",value:daysToGL>0?daysToGL:"—",sub:goLiveDate?fmtDisplay(goLiveDate):"—",color:"#0284C7",bg:"#EFF6FF"},
          {label:"% Complete",value:`${pct}%`,sub:`${done}/${total} tasks`,color:"#059669",bg:"#F0FDF4"},
          {label:"Delayed Tasks",value:delayed,sub:"need attention",color:"#DC2626",bg:"#FFF5F5"},
          {label:"CP Activities",value:rows.filter(r=>r.isCritical).length,sub:"Total float = 0",color:"#7C3AED",bg:"#F5F3FF"},
        ].map((c,i)=>(
          <div key={i} style={{background:c.bg,border:`1px solid ${c.color}30`,borderRadius:10,padding:"16px 18px"}}>
            <div style={{fontSize:24,fontWeight:800,color:c.color}}>{c.value}</div>
            <div style={{fontSize:11,fontWeight:600,color:"#374151",marginTop:3}}>{c.label}</div>
            <div style={{fontSize:9,color:"#9CA3AF",marginTop:1}}>{c.sub}</div>
          </div>
        ))}
      </div>

      <div style={{background:"#FFF",border:"1px solid #E5E7EB",borderRadius:10,padding:16,marginBottom:16}}>
        <h3 style={{margin:"0 0 12px",fontSize:12,fontWeight:700,color:"#1B2A4A"}}>Phase Progress</h3>
        {MILESTONES.map((m,i)=>{
          const {pct:p,status}=getPhase(m.start,m.end);
          return (
            <div key={i} style={{marginBottom:11}}>
              <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:3}}>
                <div style={{display:"flex",alignItems:"center",gap:6}}>
                  <span style={{width:8,height:8,borderRadius:"50%",background:rag[status],display:"inline-block"}}/>
                  <span style={{fontSize:10,fontWeight:600,color:"#374151"}}>{m.name}</span>
                </div>
                <div style={{display:"flex",alignItems:"center",gap:10}}>
                  <span style={{fontSize:9,color:"#9CA3AF"}}>{fmtDisplay(m.start)} → {fmtDisplay(m.end)}</span>
                  <span style={{fontSize:10,fontWeight:700,color:rag[status]}}>{p}%</span>
                </div>
              </div>
              <div style={{background:"#F3F4F6",borderRadius:4,height:6,overflow:"hidden"}}>
                <div style={{width:`${p}%`,height:"100%",background:rag[status],borderRadius:4,transition:"width .5s"}}/>
              </div>
            </div>
          );
        })}
      </div>

      <div style={{background:"#FFF",border:"1px solid #E5E7EB",borderRadius:10,padding:16}}>
        <h3 style={{margin:"0 0 12px",fontSize:12,fontWeight:700,color:"#1B2A4A"}}>SPOC Workload</h3>
        <div style={{display:"grid",gridTemplateColumns:"repeat(auto-fill,minmax(230px,1fr))",gap:9}}>
          {Object.entries(spocMap).sort((a,b)=>b[1].length-a[1].length).slice(0,12).map(([sp,sr])=>{
            const active=sr.filter(r=>r.status==="In-progress").length, over=active>=3;
            return (
              <div key={sp} style={{background:over?"#FFF5F5":"#F9FAFB",border:`1px solid ${over?"#FCA5A5":"#E5E7EB"}`,borderRadius:7,padding:10}}>
                <div style={{display:"flex",justifyContent:"space-between",marginBottom:6}}>
                  <span style={{fontSize:10,fontWeight:700,color:over?"#DC2626":"#374151"}}>{sp}</span>
                  {over&&<span style={{fontSize:8,background:"#DC2626",color:"#FFF",padding:"1px 5px",borderRadius:8,fontWeight:700}}>OVERLOADED</span>}
                </div>
                {sr.slice(0,3).map(r=>(
                  <div key={r.id} style={{display:"flex",justifyContent:"space-between",marginBottom:2,fontSize:9,color:"#6B7280"}}>
                    <span style={{overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap",maxWidth:140}}>{r.task}</span>
                    <span style={{background:ST_COLORS[r.status]?.bg,color:ST_COLORS[r.status]?.text,padding:"1px 4px",borderRadius:6,fontSize:8,fontWeight:600,flexShrink:0}}>{r.status}</span>
                  </div>
                ))}
                {sr.length>3&&<div style={{color:"#9CA3AF",fontSize:8}}>+{sr.length-3} more</div>}
              </div>
            );
          })}
        </div>
      </div>
    </div>
  );
}

// ─── REMINDERS MODULE ─────────────────────────────────────────────────────────
function RemindersModule({rows, projectName, goLiveDate}) {
  const [emailModal, setEmailModal] = useState(null);
  const [emailDraft, setEmailDraft] = useState("");
  const [loadingEmail, setLoadingEmail] = useState(false);
  const [copied, setCopied] = useState(false);
  const [delayAct, setDelayAct] = useState("");
  const [delayDays, setDelayDays] = useState(1);
  const [delayResult, setDelayResult] = useState(null);

  const todayD = new Date(todayStr());
  const in7 = new Date(todayD); in7.setDate(in7.getDate()+7);
  const upcoming = rows.filter(r=>{ if(!r.end)return false; const e=new Date(r.end); return e>=todayD&&e<=in7; })
    .sort((a,b)=>{ if(a.isCritical&&!b.isCritical)return -1; if(!a.isCritical&&b.isCritical)return 1; return new Date(a.end)-new Date(b.end); });

  const getDU = d=>{ const n=Math.ceil((new Date(d)-todayD)/86400000); return n===0?"Today":n===1?"Tomorrow":`In ${n}d`; };
  const urgency = row=>{ const n=Math.ceil((new Date(row.end)-todayD)/86400000); if(n<=0)return row.status!=="Done"?"red":"green"; if(n<=1)return "red"; if(n<=3)return "amber"; return "blue"; };
  const uc={red:"#DC2626",amber:"#D97706",blue:"#2563EB",green:"#059669"};

  const draftEmail = async row => {
    setEmailModal(row); setEmailDraft(""); setLoadingEmail(true);
    const ds = rows.filter(r=>r.start>=row.end&&r.fn===row.fn).slice(0,3).map(r=>r.task);
    try {
      const res = await fetch("https://api.anthropic.com/v1/messages",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({model:"claude-sonnet-4-20250514",max_tokens:1000,messages:[{role:"user",content:`Draft a professional but warm reminder email:\nProject: ${projectName||"Launch"}\nTask: ${row.task}\nFunction: ${row.fn}\nSPOC: ${row.spoc}\nEnd Date: ${fmtDisplay(row.end)}\nStatus: ${row.status}\nOn Critical Path: ${row.isCritical?"Yes":"No"}\nDownstream tasks at risk: ${ds.join(", ")||"none"}\nGo-Live: ${goLiveDate||"TBD"}\nTone: warm professional, concise, clear call to action.`}]})});
      const data = await res.json();
      setEmailDraft(data.content?.[0]?.text||"Unable to generate.");
    } catch { setEmailDraft("Unable to connect to Claude API."); }
    setLoadingEmail(false);
  };

  const calcDelay = () => {
    const act=rows.find(r=>r.task===delayAct); if(!act)return;
    const aff=rows.filter(r=>r.start>=act.end&&r.isCritical);
    const newGL=act.isCritical?new Date(new Date(goLiveDate||"2026-07-03").getTime()+delayDays*86400000*1.4):new Date(goLiveDate||"2026-07-03");
    setDelayResult({activity:act.task,days:delayDays,isCritical:act.isCritical,affectedCount:aff.length,newGL:act.isCritical?fmtDisplay(newGL):`${fmtDisplay(goLiveDate)} (no impact)`});
  };

  return (
    <div>
      <div style={{background:"#FFF",border:"1px solid #E5E7EB",borderRadius:10,padding:16,marginBottom:16}}>
        <h3 style={{margin:"0 0 12px",fontSize:12,fontWeight:700,color:"#1B2A4A"}}>⏰ Upcoming in Next 7 Days ({upcoming.length} tasks)</h3>
        {!upcoming.length?<div style={{color:"#9CA3AF",fontSize:11,padding:"14px 0"}}>No tasks due in the next 7 days.</div>
        :upcoming.map(row=>{
          const u=uc[urgency(row)],sc=ST_COLORS[row.status]||ST_COLORS["Not Started"];
          return (
            <div key={row.id} style={{display:"flex",alignItems:"center",padding:"9px 0",borderBottom:"1px solid #F3F4F6",gap:9}}>
              <div style={{width:3,height:36,background:u,borderRadius:2,flexShrink:0}}/>
              <div style={{flex:1}}>
                <div style={{display:"flex",alignItems:"center",gap:6,marginBottom:2}}>
                  {row.isCritical&&<span style={{background:"#FEE2E2",color:"#DC2626",fontSize:8,padding:"1px 5px",borderRadius:8,fontWeight:700}}>CP</span>}
                  <span style={{fontSize:10,fontWeight:600,color:"#374151"}}>{row.task}</span>
                </div>
                <div style={{display:"flex",gap:9,fontSize:9,color:"#6B7280"}}>
                  <span>👤 {row.spoc}</span><span>📅 {fmtDisplay(row.end)}</span>
                  <span style={{background:sc.bg,color:sc.text,padding:"1px 4px",borderRadius:8,fontSize:8,fontWeight:600}}>{row.status}</span>
                  <span style={{color:u,fontWeight:600}}>{getDU(row.end)}</span>
                </div>
              </div>
              <button onClick={()=>draftEmail(row)} style={{display:"flex",alignItems:"center",gap:4,padding:"5px 9px",background:"#EEF2FF",border:"1px solid #A5B4FC",borderRadius:5,cursor:"pointer",fontSize:9,color:"#4F46E5"}}><I.Mail/> Draft Email</button>
            </div>
          );
        })}
      </div>

      <div style={{background:"#FFF",border:"1px solid #E5E7EB",borderRadius:10,padding:16}}>
        <h3 style={{margin:"0 0 12px",fontSize:12,fontWeight:700,color:"#1B2A4A"}}>📊 Delay Impact Calculator</h3>
        <div style={{display:"flex",gap:9,marginBottom:12,alignItems:"flex-end"}}>
          <div style={{flex:1}}>
            <label style={{fontSize:9,color:"#6B7280",display:"block",marginBottom:3}}>Activity</label>
            <select value={delayAct} onChange={e=>setDelayAct(e.target.value)} style={{width:"100%",padding:"6px 8px",border:"1px solid #E5E7EB",borderRadius:5,fontSize:10}}>
              <option value="">-- Select --</option>
              {rows.filter(r=>r.task).map(r=><option key={r.id} value={r.task}>{r.task}</option>)}
            </select>
          </div>
          <div style={{width:80}}>
            <label style={{fontSize:9,color:"#6B7280",display:"block",marginBottom:3}}>Delay (days)</label>
            <input type="number" min="1" max="90" value={delayDays} onChange={e=>setDelayDays(parseInt(e.target.value)||1)} style={{width:"100%",padding:"6px 8px",border:"1px solid #E5E7EB",borderRadius:5,fontSize:10}}/>
          </div>
          <button onClick={calcDelay} disabled={!delayAct} style={{padding:"7px 14px",background:"#1B2A4A",color:"#FFF",border:"none",borderRadius:5,cursor:delayAct?"pointer":"not-allowed",fontSize:10,fontWeight:600}}>Calculate</button>
        </div>
        {delayResult&&(
          <div style={{background:delayResult.isCritical?"#FFF5F5":"#F0FDF4",border:`1px solid ${delayResult.isCritical?"#FCA5A5":"#BBF7D0"}`,borderRadius:7,padding:12}}>
            <div style={{fontSize:11,fontWeight:700,color:delayResult.isCritical?"#DC2626":"#059669",marginBottom:6}}>{delayResult.isCritical?"⚠️ Critical Path Impact!":"✅ No Critical Path Impact"}</div>
            <div style={{fontSize:10,color:"#374151",lineHeight:1.7}}>
              <div><strong>Activity:</strong> {delayResult.activity}</div>
              <div><strong>Delay:</strong> {delayResult.days} calendar days</div>
              <div><strong>Downstream CP activities affected:</strong> {delayResult.affectedCount}</div>
              <div><strong>New estimated Go-Live:</strong> <span style={{color:delayResult.isCritical?"#DC2626":"#059669",fontWeight:700}}>{delayResult.newGL}</span></div>
            </div>
          </div>
        )}
      </div>

      {emailModal&&(
        <div style={{position:"fixed",inset:0,background:"rgba(0,0,0,.5)",zIndex:1000,display:"flex",alignItems:"center",justifyContent:"center"}}>
          <div style={{background:"#FFF",borderRadius:14,padding:22,maxWidth:620,width:"90%",maxHeight:"80vh",overflow:"auto",boxShadow:"0 20px 50px rgba(0,0,0,.3)"}}>
            <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:12}}>
              <h3 style={{margin:0,fontSize:13,fontWeight:700,color:"#1B2A4A"}}>✉️ {emailModal.task}</h3>
              <button onClick={()=>setEmailModal(null)} style={{background:"none",border:"none",cursor:"pointer",color:"#9CA3AF"}}><I.X/></button>
            </div>
            {loadingEmail?<div style={{display:"flex",alignItems:"center",gap:9,padding:"32px 0",justifyContent:"center",color:"#6B7280"}}><div style={{width:16,height:16,border:"3px solid #E5E7EB",borderTopColor:"#6366F1",borderRadius:"50%",animation:"spin .8s linear infinite"}}/>Generating with Claude AI…</div>:(
              <>
                <div style={{background:"#F9FAFB",border:"1px solid #E5E7EB",borderRadius:7,padding:12,fontSize:10,color:"#374151",lineHeight:1.7,whiteSpace:"pre-wrap",maxHeight:360,overflow:"auto"}}>{emailDraft}</div>
                <div style={{display:"flex",gap:7,marginTop:12}}>
                  <button onClick={()=>{navigator.clipboard.writeText(emailDraft);setCopied(true);setTimeout(()=>setCopied(false),2000);}} style={{display:"flex",alignItems:"center",gap:4,padding:"6px 12px",background:copied?"#D1FAE5":"#EEF2FF",border:`1px solid ${copied?"#6EE7B7":"#A5B4FC"}`,borderRadius:5,cursor:"pointer",fontSize:10,color:copied?"#059669":"#4F46E5"}}><I.Copy/> {copied?"Copied!":"Copy"}</button>
                  <button onClick={()=>draftEmail(emailModal)} style={{padding:"6px 12px",background:"#F9FAFB",border:"1px solid #E5E7EB",borderRadius:5,cursor:"pointer",fontSize:10,color:"#374151"}}>Regenerate</button>
                </div>
              </>
            )}
          </div>
        </div>
      )}
      <style>{`@keyframes spin{to{transform:rotate(360deg);}}`}</style>
    </div>
  );
}

// ─── EXCEL PARSER ─────────────────────────────────────────────────────────────
function parseExcelRows(data) {
  const rows=[]; let id=1000; let lf="",ls="";
  for(let i=1;i<data.length;i++){
    const r=data[i]; if(!r||(!r[0]&&!r[2]))continue;
    const fn=(r[0]&&String(r[0]).trim())||lf;
    const sf=(r[1]&&String(r[1]).trim())||ls;
    if(fn)lf=fn; if(sf)ls=sf;
    const task=r[2]?String(r[2]).trim():""; if(!task)continue;
    const toDate=v=>{if(!v)return null;if(v instanceof Date)return fmtDate(v);const n=parseFloat(v);if(!isNaN(n)&&n>40000){return fmtDate(new Date(Math.round((n-25569)*86400*1000)));}const p=new Date(String(v));return isNaN(p)?null:fmtDate(p);};
    const start=toDate(r[4]),end=toDate(r[5]),revEnd=toDate(r[6]);
    const td=r[7]?parseInt(r[7])||0:calDays(start,end);
    rows.push({id:id++,fn:lf,sf:ls,task,spoc:r[3]?String(r[3]).trim():"",
      start,end,revEnd,totalDays:td,workingDays:networkDays(start,end),
      delayDays:revEnd&&end?Math.max(0,delayCalendarDays(end,revEnd)):null,
      status:r[10]?String(r[10]).trim():"Not Started",remarks:r[11]?String(r[11]).trim():"",
      isCritical:false, isNearCritical:false, floatDays:null, topoOrder:0,
      dep:null, depId:null, dep2Id:null, depElseId:null, depEnd:null});
  }
  // Compute CP on uploaded data
  const cpIds = computeCriticalPath(rows);
  return rows.map(r=>({...r,isCritical:cpIds.has(r.id)}));
}

// ─── DERIVE GO-LIVE FROM LIVE ROWS ────────────────────────────────────────────
function deriveGoLive(rows) {
  for (const t of ["Going Live on D2C","IG Post-launch"]) {
    const r=rows.find(x=>x.task===t); if(r&&r.end) return r.end;
  }
  const ends=rows.filter(r=>r.end).map(r=>r.end).sort();
  return ends[ends.length-1]||"";
}

// ─── MAIN APP ─────────────────────────────────────────────────────────────────
export default function App() {
  const [rows, setRows] = useState(DEMO_ROWS);
  const [projectName, setProjectName] = useState("Isolate Protein Powder");
  const [activeModule, setActiveModule] = useState("network");
  const [cpView, setCpView] = useState("gantt");
  const [editingProject, setEditingProject] = useState(false);
  const [showNewProject, setShowNewProject] = useState(false);
  const [lastUpdated, setLastUpdated] = useState(new Date());

  // Go-live always derived from live network
  const goLiveDate = useMemo(() => deriveGoLive(rows), [rows]);

  // ── Update a row and cascade ─────────────────────────────────────────────────
  const handleUpdate = useCallback((id, updated, doCascade) => {
    setRows(prev => {
      const next = prev.map(r => r.id===id ? updated : r);
      return doCascade ? cascadeAndCP(next) : next;
    });
    setLastUpdated(new Date());
  }, []);

  // ── Q1 FIX: Delete row — bridge depId chain so successor keeps correct predecessor ──
  const handleDelete = useCallback(id => {
    setRows(prev => {
      const target = prev.find(r=>r.id===id);
      if (!target) return prev;
      const targetDepId   = target.depId;   // deleted row's own predecessor
      const targetDep2Id  = target.dep2Id;  // deleted row's second predecessor

      const patched = prev.map(r => {
        let updated = r;

        // Bridge depId: any row that depended on the deleted row now points
        // to the deleted row's own predecessor (keeps the chain intact)
        if (r.depId === id) {
          updated = {...updated, depId: targetDepId};
        }
        // Bridge dep2Id similarly
        if (r.dep2Id === id) {
          updated = {...updated, dep2Id: targetDep2Id};
        }

        // depElse re-evaluation: if a row's PRIMARY dep (depId) was pointing
        // to the deleted row's predecessor (because it was already bridged),
        // and the row has a depElse that is now a better fit, keep depElse
        // as a fallback reference — the cascade will resolve it correctly.
        // Specifically: if the deleted row was a dep anchor (like Lab tests)
        // and a row had depElse pointing to an alternative (like V4 feedback),
        // we set depId to depElse so the fallback activates.
        if (r.depId === id && r.dep != null) {
          // The row has a depElse — use it as the new depId
          // depElse stores the original template fallback index as a row id
          // We look it up by matching template dep index to actual row id
          const depElseRow = r.depElseId != null
            ? prev.find(x => x.id === r.depElseId)
            : null;
          if (depElseRow) {
            updated = {...updated, depId: depElseRow.id};
          } else {
            updated = {...updated, depId: targetDepId};
          }
        }

        return updated;
      });

      const filtered = patched.filter(r=>r.id!==id);
      return cascadeAndCP(filtered);
    });
    setLastUpdated(new Date());
  }, []);

  // ── Q1 FIX: Add row — wire depId so new row and its successor form a proper chain ──
  const handleAddRow = useCallback(({fn, sf, task, spoc, td, afterId}) => {
    setRows(prev => {
      // Find insertion position
      const insertIdx = afterId!=null ? prev.findIndex(r=>r.id===afterId)+1 : prev.length;
      const refRow = afterId!=null ? prev.find(r=>r.id===afterId) : prev[prev.length-1];

      // New row: starts at end of refRow
      const startD = refRow ? (getEffectiveEnd(refRow)||refRow.end||todayStr()) : todayStr();
      const tdNum = parseInt(td)||0;
      const endD = tdNum>0 ? addCalendarDays(startD,tdNum) : startD;
      const newId = Date.now();
      const newRow = {
        id:newId, fn, sf, task, spoc,
        start:startD, end:endD, revEnd:null,
        totalDays:tdNum, workingDays:networkDays(startD,endD),
        delayDays:null, status:"Not Started", remarks:"",
        isCritical:false, isNearCritical:false, floatDays:null, topoOrder:0,
        dep:null, depId: refRow?refRow.id:null, dep2Id:null, depElseId:null, depEnd:null,
      };

      // Patch the row that was immediately AFTER refRow: its depId should now point to newRow
      const next = [...prev];
      next.splice(insertIdx, 0, newRow);

      // Find the row that was at insertIdx before we inserted (now at insertIdx+1)
      // and update its depId to newId if it was previously pointing to refRow
      const patched = next.map((r,i) => {
        if (i===insertIdx+1 && refRow && r.depId===refRow.id) {
          return {...r, depId: newId};
        }
        return r;
      });

      return cascadeAndCP(patched);
    });
    setLastUpdated(new Date());
  }, []);

  const handleGenerate = useCallback((generatedRows, name) => {
    setRows(generatedRows);
    setProjectName(name);
    setShowNewProject(false);
    setActiveModule("network");
    setLastUpdated(new Date());
  }, []);

  const handleUpload = async e => {
    const file=e.target.files?.[0]; if(!file)return;
    try {
      const XLSX=await import("https://cdnjs.cloudflare.com/ajax/libs/xlsx/0.18.5/xlsx.full.min.js");
      const buf=await file.arrayBuffer();
      const wb=XLSX.read(buf,{type:"array"});
      const ws=wb.Sheets["Network"]||wb.Sheets[wb.SheetNames[0]];
      const data=XLSX.utils.sheet_to_json(ws,{header:1,defval:null});
      const parsed=parseExcelRows(data);
      if(parsed.length>0){setRows(parsed);setLastUpdated(new Date());}
    } catch { alert("Failed to parse Excel file."); }
    e.target.value="";
  };

  const stats = useMemo(()=>{
    const total=rows.length, done=rows.filter(r=>r.status==="Done").length;
    const delayed=rows.filter(r=>r.status==="Delayed"||r.delayDays>0).length;
    const pct=total?Math.round((done/total)*100):0;
    const todayD=new Date(todayStr());
    const glD=goLiveDate?new Date(goLiveDate):null;
    const daysToGL=glD?Math.ceil((glD-todayD)/86400000):null;
    return {total,done,delayed,pct,daysToGL};
  },[rows,goLiveDate]);

  const nav=[
    {id:"network",   label:"Network Builder", icon:<I.Network/>},
    {id:"critical",  label:"Critical Path",   icon:<I.Gantt/>},
    {id:"dashboard", label:"Dashboard",       icon:<I.Board/>},
    {id:"reminders", label:"Reminders",       icon:<I.Bell/>},
  ];

  const glLabel  = goLiveDate ? fmtDisplay(goLiveDate) : "—";
  const tMinus   = stats.daysToGL!=null ? stats.daysToGL : "?";
  const tColor   = stats.daysToGL!=null&&stats.daysToGL<=30?"#DC2626":"#1D4ED8";
  const tBg      = stats.daysToGL!=null&&stats.daysToGL<=30?"#FFF5F5":"#EFF6FF";
  const tBorder  = stats.daysToGL!=null&&stats.daysToGL<=30?"#FCA5A5":"#BFDBFE";

  return (
    <div style={{display:"flex",height:"100vh",fontFamily:"'Segoe UI',system-ui,sans-serif",background:"#F0F4F8",overflow:"hidden"}}>
      {/* Sidebar */}
      <div style={{width:220,minWidth:220,background:"#1B2A4A",display:"flex",flexDirection:"column",boxShadow:"2px 0 8px rgba(0,0,0,.15)"}}>
        <div style={{padding:"18px 16px 14px",borderBottom:"1px solid rgba(255,255,255,.1)"}}>
          <div style={{display:"flex",alignItems:"center",gap:8,marginBottom:4}}>
            <div style={{width:28,height:28,background:"#00C896",borderRadius:7,display:"flex",alignItems:"center",justifyContent:"center",fontSize:14,fontWeight:900,color:"#1B2A4A"}}>N</div>
            <span style={{fontSize:13,fontWeight:800,color:"#FFF"}}>NetManager</span>
          </div>
          <div style={{fontSize:9,color:"#64748B"}}>Product Launch Network Tool</div>
        </div>
        <nav style={{flex:1,padding:"12px 10px"}}>
          {nav.map(item=>(
            <button key={item.id} onClick={()=>{setActiveModule(item.id);setShowNewProject(false);}}
              style={{display:"flex",alignItems:"center",gap:8,width:"100%",padding:"9px 11px",
                background:activeModule===item.id&&!showNewProject?"#00C896":"transparent",
                border:"none",borderRadius:7,cursor:"pointer",marginBottom:3,
                color:activeModule===item.id&&!showNewProject?"#1B2A4A":"#94A3B8",
                fontWeight:activeModule===item.id&&!showNewProject?700:400,fontSize:12,textAlign:"left"}}>
              {item.icon}&nbsp;{item.label}
            </button>
          ))}
          <div style={{borderTop:"1px solid rgba(255,255,255,.08)",marginTop:10,paddingTop:10}}>
            <button onClick={()=>setShowNewProject(true)}
              style={{display:"flex",alignItems:"center",gap:8,width:"100%",padding:"9px 11px",
                background:showNewProject?"#00C896":"rgba(0,200,150,.12)",
                border:"1px solid rgba(0,200,150,.3)",borderRadius:7,cursor:"pointer",
                color:showNewProject?"#1B2A4A":"#00C896",fontWeight:700,fontSize:12,textAlign:"left"}}>
              <I.New/>&nbsp;+ New Project
            </button>
          </div>
        </nav>
        <div style={{padding:"10px 12px",borderTop:"1px solid rgba(255,255,255,.08)",fontSize:9,color:"#475569"}}>
          <div>{"Updated: "+lastUpdated.toLocaleTimeString("en-IN",{hour:"2-digit",minute:"2-digit"})}</div>
          <div style={{marginTop:2}}>{stats.total+" activities | "+stats.pct+"% done"}</div>
        </div>
      </div>

      {/* Main */}
      <div style={{flex:1,display:"flex",flexDirection:"column",overflow:"hidden"}}>
        {/* Header */}
        <div style={{background:"#FFF",borderBottom:"1px solid #E5E7EB",padding:"10px 22px",display:"flex",justifyContent:"space-between",alignItems:"center",boxShadow:"0 1px 3px rgba(0,0,0,.06)"}}>
          <div style={{display:"flex",alignItems:"center",gap:10}}>
            {editingProject?(
              <input autoFocus value={projectName} onChange={e=>setProjectName(e.target.value)}
                onBlur={()=>setEditingProject(false)} onKeyDown={e=>{if(e.key==="Enter")setEditingProject(false);}}
                style={{fontSize:14,fontWeight:700,border:"2px solid #3B82F6",borderRadius:5,padding:"2px 8px",color:"#1B2A4A",outline:"none"}}/>
            ):(
              <h1 onClick={()=>setEditingProject(true)} title="Click to edit"
                style={{margin:0,fontSize:14,fontWeight:800,color:"#1B2A4A",cursor:"text"}}>{projectName}</h1>
            )}
            <span style={{fontSize:10,color:"#9CA3AF"}}>
              {"/ "+(showNewProject?"New Project":(nav.find(n=>n.id===activeModule)||{}).label)}
            </span>
          </div>
          <div style={{display:"flex",alignItems:"center",gap:9}}>
            <div style={{background:"#F0FDF4",border:"1px solid #BBF7D0",borderRadius:20,padding:"5px 14px",display:"flex",alignItems:"center",gap:6}}>
              <span style={{width:7,height:7,borderRadius:"50%",background:"#059669",display:"inline-block",flexShrink:0}}/>
              <span style={{fontSize:11,fontWeight:700,color:"#059669"}}>{"Go-Live: "+glLabel}</span>
            </div>
            <div style={{background:tBg,border:"1px solid "+tBorder,borderRadius:20,padding:"5px 14px"}}>
              <span style={{fontSize:11,fontWeight:700,color:tColor}}>{"T-"+tMinus+" days"}</span>
            </div>
            <div style={{background:"#F5F3FF",border:"1px solid #DDD6FE",borderRadius:20,padding:"5px 14px"}}>
              <span style={{fontSize:11,fontWeight:700,color:"#7C3AED"}}>{stats.pct+"% ("+stats.done+"/"+stats.total+")"}</span>
            </div>
            <label style={{display:"flex",alignItems:"center",gap:5,padding:"6px 12px",background:"#F3F4F6",border:"1px solid #E5E7EB",borderRadius:6,cursor:"pointer",fontSize:11,color:"#374151"}}>
              <I.Upload/>&nbsp;Upload Excel
              <input type="file" accept=".xlsx,.xls" onChange={handleUpload} style={{display:"none"}}/>
            </label>
          </div>
        </div>

        {/* Content */}
        <div style={{flex:1,overflow:"auto",padding:"20px"}}>
          {showNewProject&&<NewProjectBuilder onGenerate={handleGenerate} onCancel={()=>setShowNewProject(false)}/>}

          {!showNewProject&&activeModule==="network"&&(
            <div>
              <SummaryBar rows={rows} goLiveDate={goLiveDate}/>
              <div style={{background:"#FFF",borderRadius:11,padding:"16px 20px",boxShadow:"0 1px 4px rgba(0,0,0,.05)"}}>
                <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:14}}>
                  <h2 style={{margin:0,fontSize:13,fontWeight:700,color:"#1B2A4A"}}>{"📋 Network Table — "+projectName}</h2>
                  <span style={{fontSize:9,color:"#9CA3AF"}}>
                    {rows.filter(r=>r.isCritical).length+" CP tasks ⚡  |  WD = NETWORKDAYS (auto)  |  Add/delete rows auto-cascades network"}
                  </span>
                </div>
                <NetworkTable rows={rows} onUpdate={handleUpdate} onDelete={handleDelete} onAddRow={handleAddRow} projectName={projectName} goLiveDate={goLiveDate}/>
              </div>
            </div>
          )}

          {!showNewProject&&activeModule==="critical"&&(
            <div>
              <div style={{display:"flex",gap:10,marginBottom:18}}>
                {[
                  {label:"CP Activities",   value:rows.filter(r=>r.isCritical).length,color:"#EF4444",bg:"#FFF5F5"},
                  {label:"Total Float = 0", value:"Longest chain",                    color:"#7C3AED",bg:"#F5F3FF"},
                  {label:"Go-Live Date",    value:glLabel,                            color:"#059669",bg:"#F0FDF4"},
                  {label:"Days to Go-Live", value:"T-"+tMinus,                        color:"#0284C7",bg:"#EFF6FF"},
                ].map((c,i)=>(
                  <div key={i} style={{flex:1,background:c.bg,border:"1px solid "+c.color+"30",borderRadius:9,padding:"12px 15px"}}>
                    <div style={{fontSize:17,fontWeight:800,color:c.color}}>{c.value}</div>
                    <div style={{fontSize:9,color:"#6B7280",marginTop:2}}>{c.label}</div>
                  </div>
                ))}
              </div>
              <div style={{background:"#FFF",borderRadius:11,padding:"16px 20px",boxShadow:"0 1px 4px rgba(0,0,0,.05)"}}>
                <div style={{display:"flex",alignItems:"center",justifyContent:"space-between",marginBottom:14}}>
                  <h2 style={{margin:0,fontSize:13,fontWeight:700,color:"#1B2A4A"}}>{cpView==="gantt"?"📊 Gantt Chart":"🔀 Critical Path Flowchart"}</h2>
                  <div style={{display:"flex",background:"#F3F4F6",borderRadius:7,padding:2,gap:2}}>
                    {[["gantt","📊 Gantt"],["flowchart","🔀 Flowchart"]].map(([v,l])=>(
                      <button key={v} onClick={()=>setCpView(v)} style={{padding:"4px 13px",borderRadius:5,border:"none",cursor:"pointer",fontSize:11,fontWeight:600,background:cpView===v?"#1B2A4A":"transparent",color:cpView===v?"#FFF":"#6B7280"}}>{l}</button>
                    ))}
                  </div>
                </div>
                {cpView==="gantt"?<GanttChart rows={rows} goLiveDate={goLiveDate}/>:<CPFlowchart rows={rows}/>}
              </div>
              <div style={{background:"#FFF",borderRadius:11,padding:"16px 20px",marginTop:16,boxShadow:"0 1px 4px rgba(0,0,0,.05)"}}>
                <h3 style={{margin:"0 0 11px",fontSize:12,fontWeight:700,color:"#1B2A4A"}}>
                  ⚡ Critical Path Sequence — auto-computed longest chain
                </h3>
                <div style={{overflowX:"auto"}}>
                  <div style={{display:"flex",gap:4,alignItems:"center",minWidth:"max-content",paddingBottom:4}}>
                    {rows.filter(r=>r.isCritical).sort((a,b)=>(a.start||"")>(b.start||"")?1:-1).map((r,i,arr)=>(
                      <div key={r.id} style={{display:"flex",alignItems:"center",gap:4}}>
                        <div style={{background:r.status==="Done"?"#D1FAE5":"#FEE2E2",border:"1px solid "+(r.status==="Done"?"#6EE7B7":"#FCA5A5"),borderRadius:5,padding:"3px 8px",fontSize:8,fontWeight:600,color:r.status==="Done"?"#065F46":"#991B1B",whiteSpace:"nowrap"}}>
                          <div>{r.task.length>26?r.task.slice(0,26)+"…":r.task}</div>
                          <div style={{fontSize:7,color:r.status==="Done"?"#059669":"#DC2626"}}>{r.totalDays+"d | "+r.status}</div>
                        </div>
                        {i<arr.length-1&&<span style={{color:"#EF4444",fontSize:11}}>→</span>}
                      </div>
                    ))}
                  </div>
                </div>
              </div>
            </div>
          )}

          {!showNewProject&&activeModule==="dashboard"&&<DashboardModule rows={rows} goLiveDate={goLiveDate}/>}
          {!showNewProject&&activeModule==="reminders"&&<RemindersModule rows={rows} projectName={projectName} goLiveDate={goLiveDate}/>}
        </div>
      </div>
    </div>
  );
}
