/* Optional, dependency-free enhancements. Unmarked pages are untouched. */
(() => {
  "use strict";
  if (window.JehlpUI) return;
  const initialized = new WeakMap();
  let nextId = 0;
  const once = (element, name) => {
    const names = initialized.get(element) || new Set();
    if (names.has(name)) return false;
    names.add(name);
    initialized.set(element, names);
    return true;
  };
  const frame = (callback) => {
    let pending = false;
    return () => {
      if (pending) return;
      pending = true;
      window.requestAnimationFrame(() => { pending = false; callback(); });
    };
  };
  const hashTarget = (link) => {
    if (link.origin !== location.origin || link.pathname !== location.pathname || link.search !== location.search) return null;
    try { return document.getElementById(decodeURIComponent(link.hash.slice(1))); }
    catch { return null; }
  };
  const followAnchor = (event, link, target) => {
    if (event.button || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return false;
    event.preventDefault();
    if (!target.hasAttribute("tabindex")) target.setAttribute("tabindex", "-1");
    target.focus({ preventScroll: true });
    target.scrollIntoView({ block: "start" });
    if (location.hash !== link.hash) history.pushState(null, "", link.hash);
    return true;
  };

  function disclosure(button) {
    const region = document.getElementById(button.getAttribute("aria-controls"));
    if (!region || !once(button, "disclosure")) return;
    const narrow = window.matchMedia(button.dataset.disclosure || "(max-width: 42rem)");
    const closers = [...region.querySelectorAll("[data-disclosure-close]")];
    function setOpen(open, returnFocus = false) {
      const visible = !narrow.matches || open;
      region.hidden = !visible;
      button.setAttribute("aria-expanded", String(visible));
      if (returnFocus && narrow.matches) button.focus();
    }
    function layout() {
      const focusInside = region.contains(document.activeElement);
      const toggleFocused = document.activeElement === button;
      button.hidden = !narrow.matches;
      closers.forEach((close) => { close.hidden = !narrow.matches; });
      setOpen(false, focusInside);
      if (toggleFocused && !narrow.matches) {
        region.setAttribute("tabindex", "-1");
        region.focus({ preventScroll: true });
      }
    }
    button.addEventListener("click", () => setOpen(region.hidden));
    region.addEventListener("click", (event) => {
      if (!narrow.matches) return;
      const close = event.target.closest("[data-disclosure-close]");
      if (close) {
        setOpen(false, true);
        const target = document.getElementById(close.dataset.disclosureClose);
        if (target) { target.setAttribute("tabindex", "-1"); target.focus(); }
        return;
      }
      const link = event.target.closest("a[href]");
      const target = link && hashTarget(link);
      if (target && !event.button && !event.metaKey && !event.ctrlKey && !event.shiftKey && !event.altKey) {
        setOpen(false);
        followAnchor(event, link, target);
      }
    });
    const escape = (event) => {
      if (event.key === "Escape" && narrow.matches && !region.hidden) {
        event.preventDefault();
        setOpen(false, true);
      }
    };
    region.addEventListener("keydown", escape);
    button.addEventListener("keydown", escape);
    narrow.addEventListener("change", layout);
    layout();
  }

  function sectionNav(nav) {
    if (!once(nav, "nav")) return;
    const entries = [...nav.querySelectorAll("a[href]")].map((link) => ({ link, target: hashTarget(link) })).filter((entry) => entry.target);
    if (!entries.length) return;
    let active;
    const update = frame(() => {
      const offset = nav.offsetHeight + 24;
      nav.parentElement.style.setProperty("--section-offset", `${offset}px`);
      let current = entries[0];
      for (const entry of entries) if (entry.target.getBoundingClientRect().top <= offset + 8) current = entry;
      if (window.scrollY > 0 && window.innerHeight + window.scrollY >= document.documentElement.scrollHeight - 2) current = entries.at(-1);
      for (const entry of entries) {
        if (entry === current) entry.link.setAttribute("aria-current", "location");
        else entry.link.removeAttribute("aria-current");
      }
      if (active !== current && !nav.contains(document.activeElement)) {
        const linkRect = current.link.getBoundingClientRect(), navRect = nav.getBoundingClientRect();
        if (linkRect.left < navRect.left || linkRect.right > navRect.right) nav.scrollLeft += linkRect.left - navRect.left - (nav.clientWidth - linkRect.width) / 2;
      }
      active = current;
    });
    nav.addEventListener("click", (event) => {
      const entry = entries.find(({ link }) => link === event.target.closest("a"));
      if (entry) followAnchor(event, entry.link, entry.target);
    });
    window.addEventListener("scroll", update, { passive: true });
    window.addEventListener("resize", update);
    window.addEventListener("hashchange", update);
    if ("ResizeObserver" in window) {
      const observer = new ResizeObserver(update);
      observer.observe(nav);
      entries.forEach(({ target }) => observer.observe(target));
    }
    update();
  }

  function scrollRegion(region) {
    if (!once(region, "scroll")) return;
    const hint = document.createElement("p");
    hint.className = "ui-scroll-hint";
    hint.id = `ui-scroll-hint-${++nextId}`;
    hint.hidden = true;
    region.before(hint);
    const description = region.getAttribute("aria-describedby") || "";
    const update = frame(() => {
      const horizontal = region.scrollWidth > region.clientWidth + 2;
      const vertical = region.scrollHeight > region.clientHeight + 2;
      hint.hidden = !horizontal;
      region.dataset.overflow = String(horizontal);
      if (horizontal || vertical) {
        region.setAttribute("tabindex", "0");
        region.setAttribute("role", "region");
      } else {
        region.removeAttribute("tabindex");
        region.removeAttribute("role");
      }
      if (horizontal) {
        const left = region.scrollLeft > 2;
        const right = region.scrollLeft + region.clientWidth < region.scrollWidth - 2;
        hint.textContent = left && right ? "← More columns on either side →" : left ? "← More columns to the left" : "More columns to the right →";
        region.setAttribute("aria-describedby", `${description} ${hint.id}`.trim());
      } else if (description) region.setAttribute("aria-describedby", description);
      else region.removeAttribute("aria-describedby");
    });
    region.addEventListener("scroll", update, { passive: true });
    window.addEventListener("resize", update);
    if ("ResizeObserver" in window) {
      const resize = new ResizeObserver(update);
      resize.observe(region);
      const observeChildren = () => { for (const child of region.children) resize.observe(child); update(); };
      new MutationObserver(observeChildren).observe(region, { childList: true });
      observeChildren();
    }
    update();
  }

  function dialog(element) {
    if (!once(element, "dialog")) return;
    const outside = (event) => {
      const rect = element.getBoundingClientRect();
      return event.target === element && (event.clientX < rect.left || event.clientX > rect.right || event.clientY < rect.top || event.clientY > rect.bottom);
    };
    let beganOutside = false;
    element.addEventListener("pointerdown", (event) => { beganOutside = outside(event); });
    element.addEventListener("click", (event) => {
      if (beganOutside && outside(event)) element.close();
      beganOutside = false;
    });
  }

  function copyCode(pre) {
    if (!once(pre, "copy")) return;
    const code = pre.querySelector("code");
    if (!code) return;
    const button = document.createElement("button");
    button.type = "button";
    button.className = "ui-copy";
    button.textContent = "Copy";
    button.setAttribute("aria-label", "Copy code block");
    button.setAttribute("aria-live", "polite");
    let timer;
    button.addEventListener("click", async () => {
      window.clearTimeout(timer);
      try {
        await navigator.clipboard.writeText(code.textContent);
        button.textContent = "Copied";
        button.setAttribute("aria-label", "Copied code block");
      } catch {
        const range = document.createRange();
        range.selectNodeContents(code);
        const selection = window.getSelection();
        selection.removeAllRanges();
        selection.addRange(range);
        button.textContent = "Select and copy";
        button.setAttribute("aria-label", "Clipboard unavailable; code selected for manual copying");
      }
      timer = window.setTimeout(() => { button.textContent = "Copy"; button.setAttribute("aria-label", "Copy code block"); }, 1800);
    });
    pre.append(button);
  }

  // A native select remains the form/data authority; only its presentation is enhanced.
  const selects = new WeakMap();
  function selectMenu(select) {
    if (selects.has(select)) { selects.get(select)(); return; }
    if (select.multiple || select.size > 1) return;
    const wrap = document.createElement("span");
    wrap.className = "ui-select";
    const trigger = document.createElement("button");
    trigger.type = "button";
    trigger.className = "ui-select-trigger";
    trigger.setAttribute("role", "combobox");
    trigger.setAttribute("aria-haspopup", "listbox");
    trigger.setAttribute("aria-expanded", "false");
    const menu = document.createElement("span");
    menu.className = "ui-select-menu";
    menu.id = `ui-select-${++nextId}`;
    menu.setAttribute("role", "listbox");
    menu.hidden = true;
    trigger.setAttribute("aria-controls", menu.id);
    const labels = [...(select.labels || [])];
    const labelText = labels.map((label) => {
      const copy = label.cloneNode(true);
      copy.querySelectorAll("select, .ui-select").forEach((node) => node.remove());
      return copy.textContent.trim();
    }).filter(Boolean).join(" ");
    const name = select.getAttribute("aria-label") || labelText;
    if (select.hasAttribute("aria-labelledby")) trigger.setAttribute("aria-labelledby", select.getAttribute("aria-labelledby"));
    else if (name) trigger.setAttribute("aria-label", name);
    if (select.hasAttribute("aria-describedby")) trigger.setAttribute("aria-describedby", select.getAttribute("aria-describedby"));
    if (name) menu.setAttribute("aria-label", name);
    select.before(wrap);
    wrap.append(trigger, menu);
    let active = -1, items = [], search = "", searchTimer;
    const enabled = (index) => items[index] && !items[index].disabled;
    function close() {
      menu.hidden = true;
      trigger.setAttribute("aria-expanded", "false");
      trigger.removeAttribute("aria-activedescendant");
      search = "";
      window.clearTimeout(searchTimer);
    }
    function highlight(index) {
      active = index;
      items.forEach((item, i) => { item.node.dataset.active = String(i === active); });
      if (items[active]) {
        trigger.setAttribute("aria-activedescendant", items[active].node.id);
        // Scroll only this menu, never the page or an ancestor panel.
        const node = items[active].node;
        if (node.offsetTop < menu.scrollTop) menu.scrollTop = node.offsetTop;
        else if (node.offsetTop + node.offsetHeight > menu.scrollTop + menu.clientHeight) menu.scrollTop = node.offsetTop + node.offsetHeight - menu.clientHeight;
      }
    }
    function positionMenu() {
      const rect = trigger.getBoundingClientRect();
      if (rect.bottom < 0 || rect.top > window.innerHeight) { close(); return; }
      const below = window.innerHeight - rect.bottom - 12, above = rect.top - 12;
      const upward = below < 160 && above > below;
      // Compact selected values should not force longer choices into a narrow
      // column. Fit the options, but keep the whole popup inside the viewport.
      const maxWidth = Math.max(0, window.innerWidth - 16);
      menu.style.width = "max-content";
      menu.style.minWidth = `${Math.min(rect.width, maxWidth)}px`;
      menu.style.maxWidth = `${maxWidth}px`;
      menu.style.maxHeight = `${Math.max(80, Math.min(320, upward ? above : below))}px`;
      menu.style.top = upward ? "auto" : `${rect.bottom + 4}px`;
      menu.style.bottom = upward ? `${window.innerHeight - rect.top + 4}px` : "auto";
      const width = menu.getBoundingClientRect().width;
      menu.style.left = `${Math.max(8, Math.min(rect.left, window.innerWidth - width - 8))}px`;
    }
    function open() {
      if (trigger.disabled || !items.some((item) => !item.disabled)) return;
      menu.hidden = false;
      trigger.setAttribute("aria-expanded", "true");
      positionMenu();
      highlight(enabled(select.selectedIndex) ? select.selectedIndex : items.findIndex((item) => !item.disabled));
    }
    function sync() {
      trigger.textContent = select.options[select.selectedIndex]?.textContent || "Choose…";
      trigger.disabled = select.matches(":disabled");
      trigger.setAttribute("aria-required", String(select.required));
      menu.replaceChildren();
      items = [...select.options].map((option, index) => {
        const node = document.createElement("span");
        node.className = "ui-select-option";
        node.id = `${menu.id}-${index}`;
        node.dataset.optionIndex = String(index);
        node.setAttribute("role", "option");
        node.setAttribute("aria-selected", String(index === select.selectedIndex));
        const disabled = option.disabled || option.parentElement?.tagName === "OPTGROUP" && option.parentElement.disabled;
        node.setAttribute("aria-disabled", String(Boolean(disabled)));
        node.hidden = option.hidden || Boolean(option.parentElement?.tagName === "OPTGROUP" && option.parentElement.hidden);
        node.textContent = option.textContent;
        menu.append(node);
        return { node, disabled: disabled || node.hidden };
      });
      if (trigger.disabled) close();
      else if (!menu.hidden) {
        positionMenu();
        if (!menu.hidden) highlight(enabled(active) ? active : select.selectedIndex);
      }
    }
    function choose(index) {
      if (!enabled(index)) return;
      const changed = select.selectedIndex !== index;
      select.selectedIndex = index;
      close();
      sync();
      trigger.focus({ preventScroll: true });
      if (changed) {
        select.dispatchEvent(new Event("input", { bubbles: true }));
        select.dispatchEvent(new Event("change", { bubbles: true }));
      }
    }
    trigger.addEventListener("click", () => { if (menu.hidden) open(); else close(); });
    trigger.addEventListener("keydown", (event) => {
      if (event.key === "Tab") { close(); return; }
      if (event.key === "Escape") { if (!menu.hidden) { event.preventDefault(); close(); } return; }
      if (event.key === "Enter" || event.key === " " && !search) {
        event.preventDefault();
        if (menu.hidden) open(); else choose(active);
        return;
      }
      if (["ArrowDown", "ArrowUp", "Home", "End"].includes(event.key)) {
        event.preventDefault();
        if (menu.hidden) { open(); if (!["Home", "End"].includes(event.key)) return; }
        const step = event.key === "ArrowUp" || event.key === "End" ? -1 : 1;
        let index = event.key === "Home" ? 0 : event.key === "End" ? items.length - 1 : active + step;
        while (index >= 0 && index < items.length && !enabled(index)) index += step;
        if (enabled(index)) highlight(index);
        return;
      }
      if (event.key.length === 1 && !event.altKey && !event.ctrlKey && !event.metaKey) {
        event.preventDefault();
        if (menu.hidden) open();
        window.clearTimeout(searchTimer);
        search += event.key.toLocaleLowerCase();
        const query = [...search].every((letter) => letter === search[0]) ? search[0] : search;
        const start = query.length === 1 ? active + 1 : active;
        for (let offset = 0; offset < items.length; offset++) {
          const index = (Math.max(0, start) + offset) % items.length;
          if (enabled(index) && items[index].node.textContent.trim().toLocaleLowerCase().startsWith(query)) { highlight(index); break; }
        }
        searchTimer = window.setTimeout(() => { search = ""; }, 700);
      }
    });
    menu.addEventListener("mousedown", (event) => event.preventDefault());
    menu.addEventListener("click", (event) => {
      const option = event.target.closest("[data-option-index]");
      if (option) choose(Number(option.dataset.optionIndex));
    });
    document.addEventListener("pointerdown", (event) => { if (!wrap.contains(event.target)) close(); });
    trigger.addEventListener("blur", close);
    window.addEventListener("resize", close);
    window.addEventListener("scroll", (event) => { if (!menu.hidden && !menu.contains(event.target)) positionMenu(); }, true);
    labels.forEach((label) => label.addEventListener("click", (event) => {
      if (!wrap.contains(event.target) && !event.target.closest("a, button, input")) { event.preventDefault(); trigger.focus(); }
    }));
    select.addEventListener("change", sync);
    select.addEventListener("invalid", (event) => { event.preventDefault(); trigger.focus(); open(); });
    select.form?.addEventListener("reset", () => window.setTimeout(() => { close(); sync(); }, 0));
    if ("MutationObserver" in window) new MutationObserver(sync).observe(select, { childList: true, subtree: true, attributes: true, attributeFilter: ["disabled", "selected", "label", "hidden", "required"] });
    selects.set(select, sync);
    sync();
    select.hidden = true;
  }

  function enhance(root = document) {
    for (const [selector, setup] of [["[data-disclosure]", disclosure], ["[data-section-nav]", sectionNav], ["[data-scroll-region]", scrollRegion], ["dialog[data-dialog]", dialog], ["pre[data-copy-code]", copyCode], ["select[data-ui-select]", selectMenu]]) {
      if (root.matches?.(selector)) setup(root);
      root.querySelectorAll(selector).forEach(setup);
    }
  }
  window.JehlpUI = Object.freeze({ enhance });
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", () => enhance(), { once: true });
  else enhance();
})();
