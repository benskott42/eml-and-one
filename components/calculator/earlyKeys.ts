/**
 * Capture clicks and 1/E key presses that arrive before the page is listening,
 * in the order they happen, then let the calculator replay them once.
 */
export const EARLY_KEY_SCRIPT = `
window.__emlEarly = window.__emlEarly || [];
window.__emlLive = false;
function emlQueue(kind, event) {
  window.__emlEarly.push(kind);
  event.preventDefault();
  event.stopImmediatePropagation();
}
document.addEventListener("click", function (event) {
  if (window.__emlLive) return;
  var node = event.target;
  if (!node || !node.closest) return;
  var button = node.closest(".ti-btn-one, .ti-btn-eml");
  if (!button) return;
  emlQueue(button.classList.contains("ti-btn-one") ? "1" : "E", event);
}, true);
document.addEventListener("keydown", function (event) {
  if (window.__emlLive) return;
  if (event.repeat || event.metaKey || event.ctrlKey || event.altKey) return;
  var target = event.target;
  var inField = target && target.closest && target.closest("input, textarea");
  if (event.key === "Enter") {
    if (inField && target.id !== "expression") return;
    emlQueue("Enter", event);
    return;
  }
  if (inField) return;
  if (event.key === "1") emlQueue("1", event);
  else if (event.key === "e" || event.key === "E") emlQueue("E", event);
  else if (event.key === "Backspace") emlQueue("B", event);
}, true);
`;
