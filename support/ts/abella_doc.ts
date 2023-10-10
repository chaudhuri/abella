// Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
// Copyright (C) 2023  Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

function makeSafe(txt: string): string {
  return new Option(txt).innerHTML;
}

type CommandKind = "top_command" | "proof_command" | "any_command";

type RexHandler = {
  test: (k: CommandKind) => boolean;
  rex: RegExp;
  style: string;
};

const rexHandlers: Array<RexHandler> = [
  {
    // op_re
    test: (_) => true,
    rex: /(=(?:&gt;)?|\|-|-&gt;|\\\/?|\/\\|\{|\})/g,
    style: "color:#9d1f1f;",
  },
  {
    // type_re
    test: (_) => true,
    rex: /\b(list|prop|o)\b/g,
    style: "color:#1640b0;",
  },
  {
    // term_re
    test: (_) => true,
    rex: /\b(forall|exists|nabla|pi|sigma|sig|module|end)\b/g,
    style: "color:#9d1f1f;",
  },
  {
    // top_builtin_re
    test: (k) => k === "top_command",
    rex: /\b(Import|Specification|Query|Set|Show|Close)\b/g,
    style: "color:#338fff;",
  },
  {
    // top_command_re
    test: (k) => k === "top_command",
    rex: /\b((?:Co)?Define|Theorem|Split|by|Kind|Type)\b/g,
    style: "color:#9d1f1f;font-weight:bold;",
  },
  {
    // proof_command_re
    test: (k) => k === "proof_command",
    rex: /\b(abbrev|all|apply|assert|backchain|case|clear|(?:co)?induction|cut|inst|intros|keep|left|monotone|on|permute|rename|right|search|split(?:\*)?|to|unabbrev|unfold|with|witness)\b/g,
    style: "color:#9d1f1f;font-style:italic;",
  },
  {
    // proof_special_re
    test: (k) => k === "proof_command",
    rex: /\b(skip|undo|abort)\b/g,
    style: "background-color:#9d1f1f;color:#c0965b;font-weight:bold;",
  },
];

export function fontify(txt: string, kind?: CommandKind): string {
  txt = makeSafe(txt);
  rexHandlers.forEach((hnd) => {
    if (!kind || hnd.test(kind))
      txt = txt.replaceAll(hnd.rex, `<span style=${hnd.style}>$1</span>`);
  });
  return txt;
}

type SequentObj = {
  vars: string[2][];
  hyps: string[2][];
  goal: string;
  more: number;
  name?: string;
}

function bg(count: number): string {
  return (count & 1) === 0 ? "rl-even" : "rl-odd";
}

function sequentToString(obj: SequentObj, doInsts: boolean): string {
  let repr = '<div class="rl">';
  if (obj.name)
    repr += `<div><span class="rl-name">Subgoal ${obj.name}</span></div>`;
  let count = 0;
  if (obj.vars && obj.vars.length > 0) {
    const vars: string[] = [];
    const insts: string[2][] = [];
    obj.vars.forEach((v) => {
      if (v[1]) insts.push(v);
      else vars.push(v[0]);
    });
    if (vars.length)
      repr += `<div class="${bg(count++)}"><code>Variables: ${vars.join(" ")}</code></div>`;
    if (doInsts)
      insts.forEach((v) => {
        repr += `<div class="${bg(count++)}"><code>  ${v[0]} &larr; ${v[1]}</code></div>`;
      });
  }
  obj.hyps.forEach((h) => {
    repr += `<div class="${bg(count++)}"><code><span class="rl-hyp">${h[0]}</span>: ${fontify(h[1])}</code></div>`;
  });
  repr += '<div class="rl-line"></div>';
  repr += `<div>&nbsp;<code>${fontify(obj.goal)}</code></div>`;
  if (obj.more > 0)
    repr += `<div class="rl-more">(+ ${obj.more} more subgoal${obj.more > 1 ? "s" : ""})</div>`;
  repr += '</div>';
  return repr;
}

function fontifySlice(src: string, start: number, stop: number): string {
  let txt = src.slice(start, stop);
  return fontify(txt);
}

function isPresent<A>(arg: A | undefined): A {
  if (arg === undefined) throw new Error("Bug: isPresent()");
  return arg;
}

export class Content {
  readonly source: string;
  marks: Array<[number, string]>;
  private dirty: boolean;

  constructor(source: string) {
    this.source = source;
    this.marks = new Array();
    this.dirty = false;
  }

  addMark(pos: number, thing: string) {
    if (pos < 0 || pos > this.source.length)
      throw new Error(`bug: Content.addMark(${pos}, ${thing})`);
    this.marks.push([pos, thing]);
    this.dirty = true;          // [HACK] optimizable?
  }

  fontify(start: number, stop: number, rex: RegExp, cls: string) {
    if (start < 0 || start > stop || stop > this.source.length)
      throw new Error(`bug: Content.fontify(${start}, ${stop}, ..., ${cls})`);
    const extract = this.source.slice(start, stop);
    for (let match of extract.matchAll(rex)) {
      const matchStart = start + isPresent(match.index);
      const matchStop = matchStart + match[0].length;
      if (matchStop > stop) continue;
      this.addMark(matchStart, `<span class="${cls}">`);
      this.addMark(matchStop, `</span>`);
    }
  }

  toString(): string {
    if (this.dirty) {
      this.marks.sort((a, b) => a[0] - b[0]);
      this.dirty = false;
    }
    const marks = this.marks.values();
    let result = "";
    let curPos = 0;
    while (curPos < this.source.length) {
      const next = marks.next();
      if (next.done) break;
      const [nextMarkPos, nextMark] = next.value;
      if (nextMarkPos < curPos)
        throw new Error(`bug: Content.toString(curPos = ${curPos}, nextMarkPos = ${nextMarkPos})`);
      result += makeSafe(this.source.slice(curPos, nextMarkPos));
      curPos = nextMarkPos;
      result += nextMark;
    }
    if (curPos < this.source.length)
      result += makeSafe(this.source.slice(curPos, this.source.length));
    return result;
  }
}

const opRex = /(=(?:>)?|\|-|->|\\\/?|\/\\|\{|\})/g;
const typeRex = /\b(list|prop|o)\b/g;
const termRex = /\b(forall|exists|nabla|pi|sigma|sig|module|end)\b/g;
const topBuiltRex = /\b(Import|Specification|Query|Set|Show|Close)\b/g;
const topCmdRex = /\b((?:Co)?Define|Theorem|Split|by|Kind|Type)\b/g;
const proofCmdRex = /\b(abbrev|all|apply|assert|backchain|case|clear|(?:co)?induction|cut|inst|intros|keep|left|monotone|on|permute|rename|right|search|split(?:\*)?|to|unabbrev|unfold|with|witness)\b/g;
const proofSpecRex = /\b(skip|undo|abort)\b/g;


export async function loadModule(boxId: string, thmfile: string, jsonfile: string) {
  const thmBox = document.getElementById(boxId);
  if (!thmBox) throw new Error("cannot find #thmbox");
  thmBox.replaceChildren();
  // get data
  const init: RequestInit = {
    method: "GET",
    cache: "no-store",
    headers: { pragma: "no-cache" },
  };
  const thmText = new Content(await fetch(thmfile, init).then(resp => resp.text()));
  const runData = await fetch(jsonfile, init).then(resp => resp.json()) as any[];
  // map data to chunks
  const chunkMap = new Map<number, any>();
  runData.forEach((elm) => { if (elm.id) chunkMap.set(elm.id, elm); });
  // markup source into chunk divs
  chunkMap.forEach((elm, _) => {
    if (elm["type"] === "top_command" || elm["type"] === "proof_command") {
      const [start, , , stop, , ] = elm.range;
      thmText.addMark(start, `<div id="chunk-${elm.id}" class="ab-chunk">`);
      thmText.addMark(stop, '</div>');
      thmText.fontify(start, stop, opRex, "s-op");
      thmText.fontify(start, stop, typeRex, "s-ty");
      thmText.fontify(start, stop, termRex, "s-tm");
      if (elm["type"] === "top_command") {
        thmText.fontify(start, stop, topBuiltRex, "s-tb");
        thmText.fontify(start, stop, topCmdRex, "s-tc");
      }
      if (elm["type"] === "proof_command") {
        thmText.fontify(start, stop, proofCmdRex, "s-pc");
        thmText.fontify(start, stop, proofSpecRex, "s-ps");
      }
    } else if (elm["type"] === "link") {
      const [start, , , stop, , ] = elm.source;
      thmText.addMark(start + 1, `<a href="${elm.url}" class="ln">`);
      thmText.addMark(stop - 1, '</a>');
    }
  });
  thmBox.innerHTML = thmText.toString();
  // add metadata
  chunkMap.forEach((elm, _) => {
    if (elm["type"] === "system_message") {
      const target = chunkMap.get(elm.after);
      if (target && target.range) {
        const targetChunk = document.getElementById(`chunk-${elm.after}`);
        if (!targetChunk) throw new Error(`Bug: could not find chunk #${elm.after}`);
        console.log("added message", elm.message, targetChunk);
        const float = document.createElement("div");
        float.style.position = "absolute";
        float.style.zIndex = "10100";
        float.style.display = "none";
        float.innerHTML = `<span class="msg">${makeSafe(elm.message)}</span>`;
        targetChunk.addEventListener("mousemove", (ev) => {
          const flWidth = float.offsetWidth, flHeight = float.offsetHeight;
          const wWidth = window.innerWidth, wHeight = window.innerHeight;
          const pX = ev.pageX, pY = ev.pageY;
          const d = 10;
          float.style.display = "block";
          if (pX + flWidth + d <= wWidth)
            float.style.left = `${pX + d}px`;
          else
            float.style.left = `${wWidth - flWidth}px`;
          if (pY + flHeight + d <= wHeight)
            float.style.top = `${pY + d}px`;
          else if (pY - flHeight - d >= 0)
            float.style.top = `${pY - flHeight - d}px`;
          else
            float.style.display = "none"; // float doesn't fit above or below
        });
        targetChunk.addEventListener("mouseleave", () => {
          float.style.display = "none";
        });
        thmBox.append(float);
      }
    }
  });
}

/* ****


  let lastPos: number = 0;
  let cmdMap = new Map<number, [HTMLElement, any]>();
  let linkMap = new Map<number, any>();
  runData.forEach((elm) => {
    if (elm["type"] === "top_command" || elm["type"] === "proof_command") {
      const [start, , , stop, , ] = elm.range;
      const chunk = document.createElement("div");
      chunk.id = `chunk-${elm.id}`;
      chunk.classList.add("ab-chunk");
      if (lastPos < start) {
        const sp = document.createElement("span");
        sp.innerHTML = fontifySlice(thmText, lastPos, start);
        chunk.append(sp);
        lastPos = start;
      }
      const cmd = document.createElement("div");
      cmd.classList.add("ab-command",
                        elm["type"] === "proof_command" ? "ab-proof" : "ab-top");
      cmd.innerHTML = fontifySlice(thmText, start, stop);
      cmdMap.set(elm.id, [cmd, elm]);
      chunk.append(cmd);
      lastPos = stop;
      thmBox.append(chunk);
    } else if (elm["type"] === "link") {
      console.log(`Need to link URL "${elm.url}" to ${elm.parent}`);
      linkMap.set(elm.parent, elm);
    }
  });
  const thmCmds = new Set<number>();
  cmdMap.forEach(([cmd, elm], _) => {
    if (elm["type"] === "proof_command" && elm.thm_id) {
      thmCmds.add(elm.thm_id);
      const [thmCmd, _] = isPresent(cmdMap.get(elm.thm_id));
      if (thmCmd.parentNode && cmd.parentNode)
        thmCmd.parentNode.append(cmd.parentNode);
    }
  });
  const do_expand = "[expand proof]";
  const do_collapse = "[collapse proof]";
  thmCmds.forEach((thm_id) => {
    const btn = document.createElement("button");
    btn.innerText = do_collapse;
    btn.dataset.state = "expanded";
    btn.addEventListener("click", () => {
      const curState = btn.dataset.state;
      btn.dataset.state = curState === "expanded" ? "collapsed" : "expanded";
      for (let cur = btn.nextElementSibling; cur; cur = cur.nextElementSibling) {
        const curEl = cur as HTMLElement;
        if (curState === "expanded") curEl.style.display = "none";
        else curEl.style.display = "";
      }
      btn.innerText = curState === "expanded" ? do_expand : do_collapse;
    });
    const [thmCmd, _] = isPresent(cmdMap.get(thm_id));
    thmCmd.after(btn);
    const br = document.createElement("span");
    br.innerHTML = "\n";
    thmCmd.after(br);
    // btn.dispatchEvent(new Event("click", {bubbles: true}));
  });
  return cmdMap;
}

**** */
