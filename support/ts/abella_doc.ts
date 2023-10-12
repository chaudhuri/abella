// Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
// Copyright (C) 2023  Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

function makeSafe(txt: string): string {
  return new Option(txt).innerHTML;
}

type RexHandler = {
  rex: RegExp;
  style: string;
};

const rexHandlers: Array<RexHandler> = [
  {
    // op_re
    rex: /(:[:=-]?|=(?:&gt;)?|\|-|-&gt;|\\\/?|\/\\|\{|\})/g,
    style: "color:#9d1f1f;",
  },
  {
    // type_re
    rex: /\b(olist|prop|o)\b/g,
    style: "color:#1640b0;",
  },
  {
    // term_re
    rex: /\b(forall|exists|nabla|pi|sigma)\b/g,
    style: "color:#9d1f1f;",
  },
];

function fontify(txt: string): string {
  txt = makeSafe(txt);
  rexHandlers.forEach((hnd) => {
    txt = txt.replaceAll(hnd.rex, `<span style=${hnd.style}>$1</span>`);
  });
  return txt;
}

type SequentObj = {
  vars: [string, string][];
  hyps: [string, string][];
  goal: string;
  more: number;
  name?: string;
}

function bg(count: number): string {
  return (count & 1) === 0 ? "rl-even" : "rl-odd";
}

function sequentToString(obj: SequentObj, doInsts?: boolean): string {
  let repr = '<div class="rl">';
  if (obj.name)
    repr += `<div><span class="rl-name">Subgoal ${obj.name}</span></div>`;
  let count = 0;
  if (obj.vars && obj.vars.length > 0) {
    const vars: string[] = [];
    const insts: [string, string][] = [];
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

function isPresent<A>(arg: A | undefined): A {
  if (arg === undefined) throw new Error("Bug: isPresent()");
  return arg;
}

class Content {
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

const opRex = /(:[:=-]?|=(?:>)?|\|-|->|\\\/?|\/\\|\{|\}|;|\.)/g;
const typeRex = /\b(olist|prop|o)\b/g;
const termRex = /\b(forall|exists|nabla|pi|sigma|sig|module|end)\b/g;
const topBuiltRex = /\b(Import|Specification|Query|Set|Show|Close)\b/g;
const topCmdRex = /\b((?:Co)?Define|Theorem|Split|by|Kind|Type)\b/g;
const proofCmdRex = /\b(abbrev|all|apply|assert|backchain|case|clear|(?:co)?induction|cut|inst|intros|keep|left|monotone|on|permute|rename|right|search|split(?:\*)?|to|unabbrev|unfold|with|witness)\b/g;
const proofSpecRex = /\b(skip|undo|abort)\b/g;
const sigRex = /\b(type|kind)\b/g;

const do_expand = "[expand proof]";
const do_collapse = "[collapse proof]";

function getBox(boxId: string) {
  const box = document.getElementById(boxId);
  if (!box) throw new Error(`Bug: cannot find #${boxId}`);
  box.replaceChildren();
  return box;
}

class FocusBox {
  readonly box: HTMLDivElement;
  readonly inner: HTMLDivElement;
  readonly content: HTMLDivElement;

  show(html: string) {
    this.content.innerHTML = html;
    this.box.style.display = "";
    this.inner.style.width = `${this.content.offsetWidth + 40}px`;
    this.inner.style.height = `${this.content.offsetHeight + 20}px`;
  }

  close() {
      this.box.style.display = "none";
      this.content.replaceChildren();
  }

  constructor() {
    this.box = document.createElement("div");
    this.box.id = "focusbox";
    this.box.classList.add("focusbox");
    this.box.style.display = "none";
    this.inner = document.createElement("div");
    this.inner.classList.add("focusbox-inner");
    this.box.append(this.inner);
    const btnClose = document.createElement("button");
    btnClose.type = "button";
    btnClose.innerHTML = "&#xE5CD;";
    btnClose.classList.add("material-icons");
    btnClose.classList.add("focusbox-close");
    this.inner.append(btnClose);
    this.content = document.createElement("div");
    this.content.classList.add("focusbox-content");
    this.inner.append(this.content);
    btnClose.addEventListener("click", () => {
      this.close();
    });
    this.box.addEventListener("mousedown", (ev) => {
      if ((ev.target as HTMLElement).matches("#focusbox"))
        this.close();
    });
    document.addEventListener("keydown", (ev) => {
      if (ev.key === "Escape")
        this.close();
    });
    document.body.insertAdjacentElement("beforeend", this.box);
  }
}

async function loadModule(boxId: string, thmfile: string, jsonfile: string) {
  const focusBox = new FocusBox();
  const thmBox = getBox(boxId);
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
  runData.forEach((elm) => {
    if (elm.id === undefined) return;
    chunkMap.set(elm.id, elm);
  });
  // markup source into chunk divs
  runData.forEach((elm) => {
    if (elm.type === "top_command" || elm.type === "proof_command") {
      const [start, , , stop, , ] = elm.range;
      thmText.addMark(start, `<div id="chunk-${elm.id}" class="ab-command">`);
      thmText.addMark(stop, '</div>');
      thmText.fontify(start, stop, opRex, "s-op");
      thmText.fontify(start, stop, typeRex, "s-ty");
      thmText.fontify(start, stop, termRex, "s-tm");
      if (elm.type === "top_command") {
        thmText.fontify(start, stop, topBuiltRex, "s-tb");
        thmText.fontify(start, stop, topCmdRex, "s-tc");
      }
      if (elm.type === "proof_command") {
        thmText.fontify(start, stop, proofCmdRex, "s-pc");
        thmText.fontify(start, stop, proofSpecRex, "s-ps");
      }
      elm.command = makeSafe(thmText.source.slice(start, stop));
    } else if (elm.type === "link") {
      const [start, , , stop, , ] = elm.source;
      thmText.addMark(start + 1, `<a href="/${elm.url}" class="ln">`);
      thmText.addMark(stop - 1, '</a>');
    }
  });
  // insert proof begin/end tokens
  runData.forEach((elm) => {
    if (elm.type === "proof_command") {
      const stop = elm.range[3];
      const thmElm = chunkMap.get(elm.thm_id);
      if (!thmElm) throw new Error(`Bug: can't find ${elm.id} -> ${elm.thm_id}`);
      thmElm.proofStop = Math.max(stop, thmElm.proofStop ?? stop);
    }
  });
  runData.forEach((elm) => {
    if (elm.type === "top_command") {
      if (elm.proofStop) {
        thmText.addMark(elm.range[3], '<div class="ab-proof">');
        thmText.addMark(elm.proofStop, '</div>');
      }
    }
  });
  // render text
  thmBox.innerHTML = thmText.toString();
  // create the buttons
  document.querySelectorAll('div[class="ab-proof"]').forEach((el) => {
    const proofEl = el as HTMLElement;
    proofEl.style.display = "none";
    const btn = document.createElement("button");
    btn.classList.add("proof-toggle");
    btn.innerText = do_expand;
    btn.dataset.state = "C";
    btn.addEventListener("click", () => {
      const prevState = btn.dataset.state;
      if (prevState === "E") {
        btn.dataset.state = "C";
        btn.innerText = do_expand;
        proofEl.style.display = "none";
      } else {
        btn.dataset.state = "E";
        btn.innerText = do_collapse;
        proofEl.style.display = "";
      }
    });
    proofEl.before(document.createTextNode("\n"));
    proofEl.before(btn);
  });
  // create the floats
  runData.forEach((elm) => {
    elm.float = "";
    if (elm.type === "top_command" || elm.type === "proof_command") {
      if (elm.type === "top_command") {
        // elm.float += `<div class="ab-int"><span class="ab-pr">Abella &lt;</span> <strong>${elm.command}</strong></div>`;
      } else {
        const startSeq = elm.start_state as SequentObj;
        const endSeq = elm.end_state as SequentObj | undefined;
        elm.float += sequentToString(startSeq);
        elm.theorem = makeSafe(elm.theorem);
        elm.float += `<div class="ab-int"><span class="ab-pr">${elm.theorem} &lt;</span> <strong>${elm.command}</strong></div>`;
        if (endSeq) elm.float += sequentToString(endSeq);
      }
    }
  });
  // add system messages to floats
  runData.forEach((elm) => {
    if (elm.type === "system_message") {
      const cmdElm = chunkMap.get(elm.after);
      // [HACK] below, if happens, is possible Abella bug; skip
      if (cmdElm === undefined || cmdElm.float === undefined) return;
      elm.message = makeSafe(elm.message);
      cmdElm.float += `<div class="ab-sys">${elm.message}</div>`;
    }
  });
  // link the floats
  runData.forEach((elm) => {
    if (elm.float) {
      const targetChunk = document.getElementById(`chunk-${elm.id}`);
      if (!targetChunk) throw new Error(`Bug: could not find chunk #${elm.id}`);
      const float = document.createElement("div");
      float.classList.add("float")
      float.style.position = "absolute";
      float.style.zIndex = "10100";
      float.style.display = "none";
      float.innerHTML = `<div class="float-container">${elm.float}</div>`;
      targetChunk.addEventListener("mousemove", (ev) => {
        const flWidth = float.offsetWidth, flHeight = float.offsetHeight;
        const wWidth = window.innerWidth, wHeight = window.innerHeight;
        const pX = ev.pageX, pY = ev.pageY;
        const d = 10;
        let giveUp = false;
        float.style.display = "none";
        if (pX + flWidth + d <= wWidth)
          float.style.left = `${pX + d}px`;
        else
          float.style.left = `${wWidth - flWidth}px`;
        if (pY + flHeight + d <= wHeight)
          float.style.top = `${pY + d}px`;
        else if (pY - flHeight - d >= 0)
          float.style.top = `${pY - flHeight - d}px`;
        else giveUp = true; // float doesn't fit above or below
        if (!giveUp)
          float.style.display = "block";
      });
      targetChunk.addEventListener("mouseleave", () => {
        float.style.display = "none";
      });
      targetChunk.addEventListener("click", (ev) => {
        // [HACK] do nothing if it contains an a element
        if (targetChunk.querySelector("a")) {
          ev.stopPropagation();
          return false;
        }
        float.style.display = "none";
        focusBox.show(float.innerHTML);
      });
      thmBox.append(float);
    }
  });
  const btnExpandAll = document.createElement("button");
  btnExpandAll.classList.add("proof-toggle");
  btnExpandAll.textContent = "[expand all proofs]";
  btnExpandAll.addEventListener("click", () => {
    thmBox.querySelectorAll('.proof-toggle[data-state="C"]')
      .forEach((el) => {
        el.dispatchEvent(new MouseEvent("click"));
      });
  });
  const btnCollapseAll = document.createElement("button");
  btnCollapseAll.classList.add("proof-toggle");
  btnCollapseAll.textContent = "[collapse all proofs]";
  btnCollapseAll.addEventListener("click", () => {
    thmBox.querySelectorAll('.proof-toggle[data-state="E"]')
      .forEach((el) => {
        el.dispatchEvent(new MouseEvent("click"));
      });
  });
  thmBox.insertAdjacentText("afterbegin", "\n");
  thmBox.insertAdjacentElement("afterbegin", btnCollapseAll);
  thmBox.insertAdjacentText("afterbegin", " ");
  thmBox.insertAdjacentElement("afterbegin", btnExpandAll);
}

async function loadLP(sigBoxId: string, sigFile: string, sigJson: string,
                             modBoxId: string, modFile: string, modJson: string) {
  const sigBox = getBox(sigBoxId);
  const modBox = getBox(modBoxId);
  // get data
  const init: RequestInit = {
    method: "GET",
    cache: "no-store",
    headers: { pragma: "no-cache" },
  };
  const sigText = new Content(await fetch(sigFile, init).then(resp => resp.text()));
  const sigData = await fetch(sigJson, init).then(resp => resp.json()) as any[];
  const modText = new Content(await fetch(modFile, init).then(resp => resp.text()));
  const modData = await fetch(modJson, init).then(resp => resp.json()) as any[];
  sigData.forEach((annot) => {
    if (annot.kind === "name") {
      sigText.addMark(annot.range[0], '<span class="s-op">');
      sigText.addMark(annot.range[1], '</span>');
    } else if (annot.kind === "accum_sig") {
      const [start, stop] = annot.range;
      const extSig = sigText.source.slice(start, stop);
      sigText.addMark(start, `<a href="./${extSig}.lp.html" class="ln">`);
      sigText.addMark(stop, '</a>');
    } else if (annot.kind === "decl") {
      const [start, stop] = annot.range;
      sigText.addMark(start, '<div class="ab-command">');
      sigText.fontify(start, stop, opRex, "s-op");
      sigText.fontify(start, stop, typeRex, "s-ty");
      sigText.fontify(start, stop, termRex, "s-tm");
      sigText.fontify(start, stop, sigRex, "s-op");
      sigText.addMark(stop, '</div>');
    }
  });
  sigBox.innerHTML = sigText.toString();
  modData.forEach((annot) => {
    if (annot.kind === "name") {
      modText.addMark(annot.range[0], '<span class="s-op">');
      modText.addMark(annot.range[1], '</span>');
    } else if (annot.kind === "accum") {
      const [start, stop] = annot.range;
      const extMod = modText.source.slice(start, stop);
      modText.addMark(start, `<a href="./${extMod}.lp.html" class="ln">`);
      modText.addMark(stop, '</a>');
    } else if (annot.kind === "clause") {
      const [start, stop] = annot.range;
      modText.addMark(start, '<div class="ab-command">');
      modText.fontify(start, stop, opRex, "s-op");
      modText.fontify(start, stop, typeRex, "s-ty");
      modText.fontify(start, stop, termRex, "s-tm");
      modText.fontify(start, stop, sigRex, "s-tc");
      modText.addMark(stop, '</div>');
    }
  });
  modBox.innerHTML = modText.toString();
}

(window as any)["loadModule"] = loadModule;
(window as any)["loadLP"] = loadLP;
