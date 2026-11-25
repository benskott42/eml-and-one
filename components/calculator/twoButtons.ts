// The two-button layout choice, kept in localStorage and shared by every subscriber.
const TWO_BUTTONS_KEY = "eml-and-one-two-buttons";
let twoButtonsStored = false;
let twoButtonsLoaded = false;
const twoButtonsListeners = new Set<() => void>();


export function subscribeTwoButtons(listener: () => void) {
  twoButtonsListeners.add(listener);
  const onStorage = (event: StorageEvent) => {
    if (event.key !== TWO_BUTTONS_KEY) return;
    const next = event.newValue === "1";
    twoButtonsStored = next;
    twoButtonsLoaded = true;
    document.documentElement.classList.toggle("ti-two-buttons", next);
    listener();
  };
  if (typeof window !== "undefined") window.addEventListener("storage", onStorage);
  return () => {
    twoButtonsListeners.delete(listener);
    if (typeof window !== "undefined") window.removeEventListener("storage", onStorage);
  };
}

export function readTwoButtons() {
  if (!twoButtonsLoaded) {
    twoButtonsLoaded = true;
    try {
      twoButtonsStored = window.localStorage.getItem(TWO_BUTTONS_KEY) === "1";
    } catch {
      twoButtonsStored = false;
    }
  }
  return twoButtonsStored;
}

export function writeTwoButtons(value: boolean) {
  twoButtonsStored = value;
  twoButtonsLoaded = true;
  try {
    window.localStorage.setItem(TWO_BUTTONS_KEY, value ? "1" : "0");
  } catch {
    /* private mode and blocked storage still toggle for this visit */
  }
  document.documentElement.classList.toggle("ti-two-buttons", value);
  for (const listener of twoButtonsListeners) listener();
}
