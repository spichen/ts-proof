function unavailable(name) {
  throw new Error(
    `@ts-proof/proof ${name} is a verification-time marker. It has no runtime behavior, and calling it does not discharge a lemma.`
  );
}

export function prove() {
  return unavailable("prove");
}
export function lemma() {
  return unavailable("lemma");
}
