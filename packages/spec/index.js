function unavailable(name) {
  throw new Error(
    `@ts-proof/spec ${name} is a verification-time marker. It has no runtime behavior, and calling it does not prove a property.`
  );
}

export function law() {
  return unavailable("law");
}
export function endpointLaw() {
  return unavailable("endpointLaw");
}
export function external() {
  return unavailable("external");
}
export function externalNamespace() {
  return unavailable("externalNamespace");
}
export function int() {
  return unavailable("int");
}
export function bool() {
  return unavailable("bool");
}
export function string() {
  return unavailable("string");
}
export function implies() {
  return unavailable("implies");
}
export function call() {
  return unavailable("call");
}
