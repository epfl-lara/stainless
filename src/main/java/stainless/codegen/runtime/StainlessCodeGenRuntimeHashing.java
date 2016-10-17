/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.codegen.runtime;

// MurmurHash3, reproduced from std. Scala lib.
public final class StainlessCodeGenRuntimeHashing {
  public static int seqHash(Object[] elements, int seed) {
    // I feel good about this line.
    int h = avalanche(seed ^ 0xcafebabe);
    int sz = elements.length;
    if(sz == 0) return h;
      for (Object element : elements) {
        h = mix(h, element.hashCode());
      }
    return finalizeHash(h, sz);
  }

  private static int mix(int hash, int data) {
    int h = mixLast(hash, data);
    h = Integer.rotateLeft(h, 13);
    return h * 5 + 0xe6546b64;
  }

  private static int mixLast(int hash, int data) {
    int k = data;
    k *= 0xcc9e2d51;
    k  = Integer.rotateLeft(k, 15);
    k *= 0x1b873593;
    return hash ^ k;
  }

  private static int finalizeHash(int hash, int length) {
    return avalanche(hash ^ length);
  }

  private static int avalanche(int hash) {
    int h = hash;
    h ^= h >>> 16;
    h *= 0x85ebca6b;
    h ^= h >>> 13;
    h *= 0xc2b2ae35;
    h ^= h >>> 16;
    return h;
  }
}
