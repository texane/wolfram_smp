/* reference: www.cs.bell-labs.com/who/dmr/rocrypt.ps */


#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#if 0
/* conflict with stack_t */
#include <signal.h>
#else
typedef void (*sighandler_t)(int);
sighandler_t signal(int signum, sighandler_t handler);
#define SIGINT 2
#endif
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>


/* crypto block size */
#define block_size 256


/* sigint handler */

static volatile unsigned int is_sigint = 0;

static void on_sigint(int x)
{
  is_sigint = 1;
}

static size_t make_index(size_t j, size_t i)
{
  /* return an absolute index given j, i */
  return j * block_size + i;
}

static uint8_t mod(int x)
{
  return (uint8_t)(x % (int)block_size);
}

static void compute_inverse(const uint8_t* x, uint8_t* inv)
{
  /* compute the inverse permutation */
  size_t i;
  for (i = 0; i < block_size; ++i) inv[x[i]] = i;
}

static void check_a
(
 uint8_t* a, uint8_t* am,
 const uint8_t* c, const uint8_t* p, const uint8_t* pm, size_t n
)
{
  /* from section 3.1 */
  /* aj[ci + i] = pi + i; */
  /* aj[pi + i] = ci + i; */
  /* check a for any inconsistency based on */

  size_t ipi_map[block_size];
  size_t ici_map[block_size];

  const size_t block_count = n / block_size;

  size_t i;
  size_t j;

  for (j = 0; j < block_count; ++j)
  {
    memset(ipi_map, 0, sizeof(ipi_map));
    memset(ici_map, 0, sizeof(ici_map));

    for (i = 0; i < block_size; ++i)
    {
      if (pm[i] == 0) continue ;

      const size_t ij = make_index(j, i);

      const uint8_t ipi = mod((int)i + (int)p[i]);
      const uint8_t ici = mod((int)i + (int)c[i]);

      if (am[ipi] && (a[ipi] != ici))
      {
	printf("ipi conflict\n");
	printf("pos: 0x%04x(%c) was: 0x%04x(%c)\n", ij, p[i], ipi_map[ipi], p[ipi_map[ipi]]);
	getchar();
      }

      if (am[ici] && (a[ici] != ipi))
      {
	printf("ici conflict\n");
	printf("pos: 0x%04x(%c) was: 0x%04x(%c)\n", ij, p[i], ici_map[ici], p[ici_map[ici]]);
	getchar();
      }

      ici_map[ici] = ij;
      ipi_map[ipi] = ij;
    }

    /* advance so that j is dropped */
    a += block_size;
    am += block_size;
    p += block_size;
    pm += block_size;
    c += block_size;
  }
}

static void compute_a
(
 uint8_t* a, uint8_t* am,
 const uint8_t* c, const uint8_t* p, const uint8_t* pm,
 size_t block_count
)
{
  /* recover a from a given cryptoblock */

  /* a the resulting vector */
  /* am the a map */
  /* c the cipher text */
  /* p the plain text */
  /* pm the plain map */

  /* from section 3.1 */
  /* a[ci + i] = pi + i; */
  /* a[pi + i] = ci + i; */

  size_t j;
  size_t i;

  for (j = 0; j < block_count; ++j)
  {
    memset(am, 0, block_size);

    for (i = 0; i < block_size; ++i)
    {
      if (pm[i] == 0) continue ;

      const uint8_t ipi = mod((int)i + (int)p[i]);
      const uint8_t ici = mod((int)i + (int)c[i]);

      am[ipi] = 1;
      am[ici] = 1;

      a[ipi] = ici;
      a[ici] = ipi;
    }

    /* advance so that j is dropped */
    a += block_size;
    am += block_size;
    p += block_size;
    pm += block_size;
    c += block_size;
  }
}

typedef struct
{
  size_t i;

#define STACK_MAX_SIZE 512
  union
  {
    size_t aji;
    size_t jzi;
    size_t x;
  } p[STACK_MAX_SIZE];

} stack_t;

static void stack_init(stack_t* s)
{
  s->i = 0;
}

static void stack_push(stack_t* s, size_t x)
{
  if (s->i == STACK_MAX_SIZE)
  {
    printf("stack overflow\n");
    exit(-1);
  }

  s->p[s->i].x = x;
  ++s->i;
}

static void stack_pop(stack_t* s, size_t* x)
{
  --s->i;
  *x = s->p[s->i].x;
}

static size_t stack_occupancy(const stack_t* s)
{
  return s->i;
}

static unsigned int stack_is_full(const stack_t* s)
{
  return stack_occupancy(s) == STACK_MAX_SIZE;
}

static void stack_clear(stack_t* s)
{
  s->i = 0;
}

static void unprop_az
(
 uint8_t* a, uint8_t* am,
 uint8_t* z, uint8_t* zm,
 uint8_t* zi, uint8_t* zim,
 size_t block_count,
 stack_t* astack,
 stack_t* zstack
)
{
  while (stack_occupancy(zstack))
  {
    size_t aji;
    stack_pop(zstack, &aji);

#if 1 /* debug */
    if (zim[z[aji]] == 0)
    {
      printf("error popping zi[%u]\n", z[aji]);
      exit(-1);
    }
#endif

#if 1 /* debug */
    if (zm[aji] == 0)
    {
      printf("error popping z[%u]\n", aji);
      exit(-1);
    }
#endif

    zim[z[aji]] = 0;
    zm[aji] = 0;
  }

  while (stack_occupancy(astack))
  {
    size_t jzi;
    stack_pop(astack, &jzi);

#if 1 /* debug */
    if (am[jzi] == 0)
    {
      printf("error popping a[%u]\n", jzi);
      exit(-1);
    }
#endif

    am[jzi] = 0;
  }
}

static size_t prop_az
(
 uint8_t* a, uint8_t* am,
 uint8_t* z, uint8_t* zm,
 uint8_t* zi, uint8_t* zim,
 size_t block_count,
 stack_t* astack,
 stack_t* zstack
)
{
  /* recompute a and z according to section 4: */
  /* z[aj+1[i]] = aj[z[i]] */

  size_t nz;
  size_t i;
  size_t j;

  stack_init(astack);
  stack_init(zstack);

  nz = 0;

  for (j = 0; j < block_count - 1; ++j)
  {
    for (i = 0; i < block_size; ++i)
    {
      if (zm[i] == 0) continue ;
      const size_t jzi = make_index(j, z[i]);

      const size_t ji = make_index(j + 1, i);
      if (am[ji] == 0) continue ;

      const size_t aji = a[ji];

      /* both unknwon */
      if ((am[jzi] == 0) && (zm[aji] == 0))
      {
	continue ;
      }
      if ((am[jzi] == 1) && (zm[aji] == 1))
      {
	/* both known, check validity */
	if (z[aji] != a[jzi]) return (size_t)-1;
      }
      else if (zm[aji] == 0)
      {
	if (zim[a[jzi]] == 1)
	{
	  /* z^-1[a[jzi]] = x */
	  /* means z[x] = a[jzi] */
	  /* and x must equals aji */

	  if (zi[a[jzi]] != aji)
	  {
	    /* inconsistent */
	    return (size_t)-1;
	  }

	  /* already pushed */
	  continue ;
	}

	/* z[aj+1[i]] unknown */
	z[aji] = a[jzi];
	zm[aji] = 1;
	zi[a[jzi]] = aji;
	zim[a[jzi]] = 1;
	++nz;

	stack_push(zstack, aji);
      }
      else if (am[jzi] == 0)
      {
	/* must hold: z[aj+1[i]] = aj[z[i]] */

	/* aj[z[i]] unknown */
	a[jzi] = z[aji];
	am[jzi] = 1;

	stack_push(astack, jzi);
      }
    }
  }

  return nz;
}

static int check_z
(
 uint8_t* a, uint8_t* am,
 uint8_t* z, uint8_t* zm,
 uint8_t* zi, uint8_t* zim,
 size_t block_count
)
{
  /* section 4 */
  /* z[aj+1[i]] = aj[z[i]] */

  size_t n;
  size_t i;
  size_t j;

  for (j = 0; j < block_count; ++j)
  {
    for (i = 0; i < block_size; ++i)
    {
      if (zm[i] == 0) continue ;
      const size_t jzi = make_index(j, z[i]);
      if (am[jzi] == 0) continue ;

      const size_t ji = make_index(j + 1, i);
      if (am[ji] == 0) continue ;

      if ((zm[a[ji]] == 1) && (z[a[ji]] != a[jzi]))
      {
#if 0 /* test */
	printf("WOULD_HAVE_BEEN_INVALID\n");
	printf("a[%u,%u] == 0x%02x\n", j + 1, i, a[ji]);
	printf("a[%u,%u] == 0x%02x\n", j, z[i], a[jzi]);
	getchar();
#endif
	return -1;
      }
    }
  }

  return 0;
}

static size_t init_z
(
 const uint8_t* c, const uint8_t* p, const uint8_t* pm,
 uint8_t* a, uint8_t* am,
 uint8_t* z, uint8_t* zm,
 uint8_t* zi, uint8_t* zim,
 size_t block_count
)
{
#if 0

  /* from section 3.1: a_j[i + cij] = i + pij */
  /* thus: pij = a_j[i + cij] - i */
  /* from section 4: a_j[i] = z^-1[a_j-1[z[i]]] */
  /* thus: a_j[i + cij] = z^-1[a_j-1[z[i + cij]]] */
  /* thus: pij = z^-1[a_j-1[z[i + cij]]] - i (1) */
  /* and: cij = z^-1[a_j-1[z[i + pij]]] - i (2) */
  /* assume: z[i + cij] = x */
  /* then: (1) must hold true for all j */
  /* assume: z[i + pij] = x */
  /* then: (2) must hold true for all j */

  const size_t n = block_count * block_size;

  size_t ij;
  size_t k;
  size_t l;
  size_t x;

  size_t nz;

  nz = 0;

  for (ij = 0; ij < n; ++ij)
  {
    const size_t i = ij % block_size;

    if (pm[ij] == 0) continue ;

    const size_t ciji = mod((int)c[ij] + (int)i);
    const size_t piji = mod((int)p[ij] + (int)i);

    if (zm[ciji] == 0)
    {
      /* assume z[ciji] = x for all x */
      for (x = 0; x < block_size; ++x)
      {
	/* z[something] = x already known */
	if (zim[x]) continue ;

	z[ciji] = x;
	zm[ciji] = 1;
	zi[x] = ciji;
	zim[x] = 1;

	/* check assumption does not violate (1) */

	size_t j;

	for (j = 1; j < block_count; ++j)
	{
	  const size_t k = make_index(j - 1, x);
	  if (am[k] == 0) goto invalid_assumption;
	  if (zim[a[k]] == 0) goto invalid_assumption;
	  if (zi[a[k]] != p[ij]) goto invalid_assumption;
	}

	/* assumption was valid */
	++nz;
	continue ;

      invalid_assumption:
	continue ;
      }

    } /* zm[ciji] == 0 */

      if (zm[ciji]) continue ;

      const size_t jx = make_index(j, x);
      if (am[jx] == 0) continue ;
      if (zim[a[jx]]) continue ;

      /* assumptions */

      size_t ciji_assumed = 0;
      size_t piji_assumed = 0;

      if (zm[ciji] == 0)
      {
	z[ciji] = x;
	zm[ciji] = 1;
	zi[x] = ciji;
	zim[x] = 1;
	ciji_assumed = 1;
      }

      if (zm[piji] == 0)
      {
	z[piji] = a[jx];
	zm[piji] = 1;
	zi[a[jx]] = piji;
	zim[a[jx]] = 1;
	piji_assumed = 1;
      }

      /* no assumptions made */
      if ((ciji_assumed + piji_assumed) == 0) continue ;

      /* check assumptions */
#if 0
      for (k = 1; k < block_count; ++k)
      {
	for (l = 0; l < block_size; ++l)
	{
	  const size_t lk = make_index(k, l);

	  /* should be goto invalid_assumptions */
	  /* but 7 blocks make it hard to reach */
	  if (pm[lk] == 0) continue ;

	  const uint8_t clkl = mod((int)c[lk] + (int)l);

	  if (clkl == (uint8_t)ciji)
	  {
	    const size_t kk = make_index(k - 1, z[clkl]);
	    if (am[kk] == 0) goto invalid_assumptions;
	    if (zim[a[kk]] == 0) goto invalid_assumptions;

	    if (mod((int)zi[a[kk]] - (int)l) != p[lk])
	      goto invalid_assumptions;
	  }
	}
      }
#else
      if (check_z(a, am, z, zm, zi, zim, block_count) == -1)
	goto invalid_assumptions;
      const size_t prop_count = prop_az
	(a, am, z, zm, zi, zi, block_count, NULL, NULL);
      if (prop_count == (size_t)-1) goto invalid_assumptions;
#endif

      nz += (ciji_assumed + piji_assumed) + prop_count;

      continue ;

    invalid_assumptions:
      if (ciji_assumed)
      {
	zm[ciji] = 0;
	zim[x] = 0;
      }
      if (piji_assumed)
      {
	zm[piji] = 0;
	zim[a[jx]] = 0;
      }
    } /* for x */
  } /* for i */

  return nz;

#else
return 0;
#endif
}


static void transform2
(
 uint8_t* p, uint8_t* pm, const uint8_t* c, size_t n,
 const uint8_t* a, const uint8_t* am,
 const uint8_t* z, const uint8_t* zm
);

static void transform_and_print
(
 const uint8_t* c,
 const uint8_t* a, const uint8_t* am,
 const uint8_t* z, const uint8_t* zm
)
{
  /* should be <= 6 */
#define BLOCK_COUNT 5

  static const size_t block_count = BLOCK_COUNT;
  uint8_t p[block_size * block_count];
  uint8_t pm[block_size * block_count];
  size_t i;

  transform2(p, pm, c, block_size * block_count, a, am, z, zm);

  printf("----\n");
  for (i = 0; i < sizeof(p); ++i)
    printf("%c", pm[i] ? p[i] : ' ');
  printf("\n");
}

static size_t transform_and_count
(
 const uint8_t* c, const uint8_t* p, const uint8_t* pm,
 const uint8_t* a, const uint8_t* am,
 const uint8_t* z, const uint8_t* zm,
 const uint8_t* zi, const uint8_t* zim
)
{
  /* given: c_j, a_j, z, z^-1 */
  /* compute: p_j+1 */
  /* return: sum(p_j+1 = actual_j+1) */

  /* j+1 is BLOCK_COUNT, the first known but unused block */
  static const size_t j = BLOCK_COUNT - 1;

  /* compute: aj+1[i] = z^-1[aj[z[i]]] */

  uint8_t aj1[block_size];
  uint8_t aj1m[block_size];

  size_t i;

  for (i = 0; i < block_size; ++i)
  {
    aj1m[i] = 0;

    if (zm[i] == 0) continue ;

    const size_t jzi = make_index(j, z[i]);
    if (am[jzi] == 0) continue ;

    if (zim[a[jzi]] == 0) continue ;

    aj1[i] = zi[a[jzi]];
    aj1m[i] = 1;
  }

  /* compute: p_ij = aj[cij + i] - i */

  size_t count = 0;

  for (i = 0; i < block_size; ++i)
  {
    const size_t ij = make_index(j + 1, i);

    if (pm[ij] == 0) continue ;

    if (aj1m[mod((int)c[ij] + (int)i)] == 0) continue ;

    const uint8_t x = mod((int)aj1[mod((int)c[ij] + (int)i)] - (int)i);
    if (x == p[ij]) ++count;
  }

  return count;
}

typedef struct solve_arg
{
  const uint8_t* c;
  const uint8_t* p;
  const uint8_t* pm;

  uint8_t* a;
  uint8_t* am;
  size_t block_count;
  uint8_t* z;
  uint8_t* zm;
  uint8_t* zi;
  uint8_t* zim;

  size_t best_zn;
  uint8_t best_az[block_size];
  uint8_t best_azm[block_size];
  uint8_t best_z[block_size];
  uint8_t best_zm[block_size];
  uint8_t best_zi[block_size];
  uint8_t best_zim[block_size];

} solve_arg_t;

static void solve_az_rec(solve_arg_t* a, size_t x, size_t zn)
{
  /* find y such that z[x] = y */
  /* that meets current constraints */
  /* and allow other x to be found */

  size_t j;
  size_t y;

  size_t best_y;
  size_t n;

  stack_t astack;
  stack_t zstack;
  stack_t uvstack;

  const size_t count = transform_and_count
    (a->c, a->p, a->pm, a->a, a->am, a->z, a->zm, a->zi, a->zim);

  if (count >= 32)
  {
    /* capture if best score */
    if (zn > a->best_zn)
    {
      a->best_zn = zn;

      /* copy only a_0 */
      memcpy(a->best_az, a->a, block_size);
      memcpy(a->best_azm, a->am, block_size);

      memcpy(a->best_z, a->z, block_size);
      memcpy(a->best_zm, a->zm, block_size);
      memcpy(a->best_zi, a->zi, block_size);
      memcpy(a->best_zim, a->zim, block_size);
    }

#if 1 /* debug */
    printf("FOUND: %u\n", count);

    /* transform_and_print(a->c, a->a, a->am, a->z, a->zm); */

    for (j = 0; j < block_size; ++j) n += a->am[j];
    printf("best_zn == %u, best_a == %u\n", a->best_zn, n);

    printf("a == \n");
    for (j = 0; j < block_size; ++j)
    {
      if (j && (j % 8 == 0)) printf("\n");
      if (a->am[j]) printf(" 0x%02x", a->a[j]);
      else printf("     ");
    }
    printf("\n");

    printf("z == \n");
    for (j = 0; j < block_size; ++j)
    {
      if (j && (j % 8 == 0)) printf("\n");
      if (a->zm[j]) printf(" 0x%02x", a->z[j]);
      else printf("     ");
    }
    printf("\n");

    getchar();
#endif
  }

  if (zn == block_size)
  {
    return ;
  }

  if (a->zm[x])
  {
    /* propagation already solved it */

#if 1 /* debug */
    /* printf("z[0x%02x] = 0x%02x done\n", x, a->z[x]); */
    if (a->zim[a->z[x]] == 0)
    {
      printf("invalid a->zim\n");
      exit(-1);
    }
    if (a->zi[a->z[x]] != x)
    {
      printf("invalid a->z[x]\n");
      exit(-1);
    }
#endif

    solve_az_rec(a, x + 1, zn);
    return ;
  }

  /* iterate over all possible z[x] = y */
  for (y = 0; y < block_size; ++y)
  {
    if (a->zim[y])
    {
#if 1 /* debug */
      /* printf("z[0x%02x] = 0x%02x done\n", x, a->z[x]); */
      if (a->zm[a->zi[y]] == 0)
      {
	printf("invalid a->zm\n");
	exit(-1);
      }
      if (a->z[a->zi[y]] != y)
      {
	printf("invalid a->z\n");
	exit(-1);
      }
#endif
      continue ;
    }

    /* check z[x] = y valid for all j */
    for (j = 0; j < a->block_count - 1; ++j)
    {
      const size_t jy = make_index(j, y);
      const size_t jx = make_index(j + 1, x);

      if (a->am[jy] == 0) continue ;
      if (a->am[jx] == 0) continue ;

      const uint8_t v = a->a[jy];
      const uint8_t u = a->a[jx];

      if ((a->zim[v] == 1) && (a->zi[v] != u))
      {
	/* invalid, would mean z[u] != v */
	break ;
      }

      if ((a->zm[u] == 1) && (a->z[u] != v))
      {
	/* invalid hypothesis */
	break ;
      }
    }

    /* invalid hypothesis, next y */
    if (j != (a->block_count - 1)) continue ;

    /* hypothesis met constraints, assume z[x] = y */
    a->z[x] = y;
    a->zm[x] = 1;
    a->zi[y] = x;
    a->zim[y] = 1;

    /* assume z[u] = v */
    stack_init(&uvstack);
#if 0
    for (j = 0; j < a->block_count - 1; ++j)
    {
      const size_t jy = make_index(j, y);
      const size_t jx = make_index(j + 1, x);

      if (a->am[jy] == 0) continue ;
      if (a->am[jx] == 0) continue ;

      const uint8_t v = a->a[jy];
      const uint8_t u = a->a[jx];

      if (a->zm[u]) continue ;
      if (a->zim[v]) continue ;

      a->z[u] = v;
      a->zm[u] = 1;
      a->zi[v] = u;
      a->zim[v] = 1;

      stack_push(&uvstack, u);
    }
#endif

    /* propagate all */
    n = prop_az
    (
     a->a, a->am,
     a->z, a->zm,
     a->zi, a->zim,
     a->block_count,
     &astack,
     &zstack
    );

    if (n == (size_t)-1)
    {
      goto invalid_hypothesis;
    }

    /* find hypothesis for z[x + 1] */
    solve_az_rec(a, x + 1, zn + stack_occupancy(&uvstack) + n + 1);

  invalid_hypothesis:
    /* undo propagate */
    unprop_az
    (
     a->a, a->am,
     a->z, a->zm,
     a->zi, a->zim,
     a->block_count,
     &astack,
     &zstack
    );

    while (stack_occupancy(&uvstack))
    {
      size_t u;
      stack_pop(&uvstack, &u);
      const size_t v = a->z[u];
      a->zim[v] = 0;
      a->zm[u] = 0;
    }

    /* undo before breaking */
    a->zm[x] = 0;
    a->zim[y] = 0;

    if (a->best_zn == block_size)
    {
      return ;
    }

    if (is_sigint)
    {
      return ;
    }

    /* next hypothesis */
  }
}

static size_t solve_az
(
 const uint8_t* c, const uint8_t* p, const uint8_t* pm,
 uint8_t* a, uint8_t* am,
 uint8_t* az, uint8_t* azm,
 size_t block_count,
 uint8_t* z, uint8_t* zm,
 uint8_t* zi, uint8_t* zim
)
{
  solve_arg_t arg;
  size_t n;

  memset(zm, 0, block_size);
  memset(zim, 0, block_size);

  arg.c = c;
  arg.p = p;
  arg.pm = pm;
  arg.a = a;
  arg.am = am;
  arg.block_count = block_count;
  arg.z = z;
  arg.zm = zm;
  arg.zi = zi;
  arg.zim = zim;

  arg.best_zn = 0;
  memset(arg.best_azm, 0, block_size);
  memset(arg.best_zm, 0, block_size);
  memset(arg.best_zim, 0, block_size);

  solve_az_rec(&arg, 0, 0);

  memcpy(az, arg.best_az, block_size);
  memcpy(azm, arg.best_azm, block_size);
  memcpy(z, arg.best_z, block_size);
  memcpy(zm, arg.best_zm, block_size);
  memcpy(zi, arg.best_zi, block_size);
  memcpy(zim, arg.best_zim, block_size);

  /* stats */
  size_t naz = 0;
  size_t nz = 0;
  size_t nzi = 0;
  size_t i;
  for (i = 0; i < block_size; ++i)
  {
    if (azm[i]) ++naz;
    if (zm[i]) ++nz;
    if (zim[i]) ++nzi;
  }
  printf("solve_az_rec: best_zn == %u, naz == %u, nz == %u, nzi == %u\n",
	 arg.best_zn, naz, nz, nzi);

  return arg.best_zn;
}

static void recover_az
(
 const uint8_t* c, const uint8_t* p, const uint8_t* pm, size_t n,
 uint8_t* az, uint8_t* azm,
 uint8_t* z, uint8_t* zm
)
{
  /* c the cipher text */
  /* p the plain text */
  /* pm the plain validity map */
  /* n the cipher and plain text sizes */
  /* az the a_0 permutation */
  /* azm the az validity map */
  /* z the zee permutation */
  /* zm the zee validity map */

  const size_t block_count = n / block_size;

  uint8_t* a;
  uint8_t* am;

  size_t j;

  uint8_t* trans_pm;
  uint8_t* trans_p;

  size_t x;
  uint8_t zim[block_size];
  uint8_t zi[block_size];

  /* compute a */
  a = malloc(block_count * block_size);
  am = malloc(block_count * block_size);
  compute_a(a, am, c, p, pm, block_count);
  check_a(a, am, c, p, pm, n);

#if 0 /* debug */
  {
    size_t i;
    size_t n = 0;
    for (i = 0; i < block_size; ++i) n += am[i];
    printf("card(a0) == %u\n", n);
  }
#endif

  /* allocate transformed buffers */
  trans_pm = malloc(n);
  trans_p = malloc(n);

  /* solve az */
  solve_az(c, p, pm, a, am, az, azm, block_count, z, zm, zi, zim);

#if 0
  for (j = 0; j < block_size; ++j)
  {
    if (j && (j % 8 == 0)) printf("\n");
    if (zm[j]) printf(" 0x%02x", z[j]);
    else printf("     ");
  }
  printf("\n");
  transform_and_print(c, a, am, z, zm);
  getchar();
#endif

  free(a);
  free(am);

  free(trans_pm);
  free(trans_p);
}


/* memory mapped file */

typedef struct mapped_file
{
  const uint8_t* base;
  size_t size;
} mapped_file_t;

#define MAPPED_FILE_INITIALIZER { NULL, 0 }

static int map_file(mapped_file_t* mf, const char* path)
{
  int error = -1;
  struct stat st;

  const int fd = open(path, O_RDONLY);
  if (fd == -1) return -1;

  if (fstat(fd, &st) == -1) goto on_error;

  mf->base = mmap(NULL, st.st_size, PROT_READ, MAP_SHARED, fd, 0);
  if (mf->base == (void*)MAP_FAILED) goto on_error;
  mf->size = st.st_size;

  /* success */
  error = 0;

 on_error:
  close(fd);

  return error;
}

static void unmap_file(mapped_file_t * mf)
{
  munmap((void*)mf->base, mf->size);
  mf->base = (void*)MAP_FAILED;
  mf->size = 0;
}

/* crypt or decrypt a text */

static void transform
(uint8_t* p, const uint8_t* c, size_t n, const uint8_t* r, const uint8_t* s)
{
  /* p the plain buffer */
  /* c the cipher buffer */
  /* n the buffer size */
  /* r the r key perm */
  /* s the s key perm */

  uint8_t rinv[block_size];
  size_t k;

  compute_inverse(r, rinv);

  for (k = 0; k < n; ++k)
  {
    const int i = (int)(k % block_size);
    const int j = (int)(k / block_size);
    p[k] = mod((int)rinv[mod((int)s[mod((int)r[mod((int)c[i] + i)] + j)] - j)] - i);
  }
}

static void transform2
(
 uint8_t* p, uint8_t* pm, const uint8_t* c, size_t n,
 const uint8_t* a, const uint8_t* am,
 const uint8_t* z, const uint8_t* zm
)
{
  /* assume all a0, z, zinv known */

  uint8_t pre_aj[block_size];
  uint8_t pre_ajm[block_size];
  uint8_t aj[block_size];
  uint8_t ajm[block_size];
  uint8_t zi[block_size];
  uint8_t zim[block_size];

  const size_t block_count = n / block_size;
  size_t i;
  size_t j;

  /* initialize zinv */
  memset(zim, 0, block_size);
  for (i = 0; i < block_size; ++i)
  {
    if (zm[i] == 0) continue ;
    zi[z[i]] = i;
    zim[z[i]] = 1;
  }

  /* initialize aj */
  for (i = 0; i < block_size; ++i)
  {
    if (am[i] == 0)
    {
      ajm[i] = 0;
      continue ;
    }

    aj[i] = a[i];
    ajm[i] = 1;
  }

  for (j = 0; j < block_count; ++j)
  {
    /* transform current block */
    for (i = 0; i < block_size; ++i)
    {
      const size_t ij = make_index(j, i);

      pm[ij] = 0;

      if (ajm[mod((int)c[ij] + (int)i)] == 0) continue ;

      p[ij] = mod((int)aj[mod((int)c[ij] + (int)i)] - (int)i);
      pm[ij] = 1;
    }

    /* compute next permutation: A_j = Z^-j A_0 Z^j */
    /* thus A_j+1 = Z^1 A_j Z */

    for (i = 0; i < block_size; ++i)
    {
      pre_aj[i] = aj[i];
      pre_ajm[i] = ajm[i];
    }

    for (i = 0; i < block_size; ++i)
    {
      ajm[i] = 0;

      if (zm[i] == 0) continue ;
      if (pre_ajm[z[i]] == 0) continue ;
      if (zim[pre_aj[z[i]]] == 0) continue ;

      aj[i] = zi[pre_aj[z[i]]];
      ajm[i] = 1;
    }
  }
}


/* main */

int main(int ac, char** av)
{
  /* usage: a.out cipher_path plain_path map_path */

  const char* const cipher_path = "../data/crypt.c.cipher";
  const char* const plain_path = "../data/crypt.c.plain";
  const char* const map_path = "../data/crypt.c.map";

  mapped_file_t cipher_mf = MAPPED_FILE_INITIALIZER;
  mapped_file_t plain_mf = MAPPED_FILE_INITIALIZER;
  mapped_file_t map_mf = MAPPED_FILE_INITIALIZER;

  uint8_t a[block_size];
  uint8_t am[block_size];
  uint8_t z[block_size];
  uint8_t zm[block_size];

  uint8_t* p;
  uint8_t* pm;
  size_t n;
  size_t i;

  map_file(&cipher_mf, cipher_path);
  map_file(&plain_mf, plain_path);
  map_file(&map_mf, map_path);

  /* translate the map from dollar based to 0 or 1 */
  pm = malloc(plain_mf.size);
  for (i = 0; i < plain_mf.size; ++i)
  {
    uint8_t x = 1;
    if (map_mf.base[i] == '$')
    {
      x = 0;
    }
#if 0 /* skip linefeed and tabs */
    else
    {
      
      const uint8_t c = plain_mf.base[i];
      if ((c == '\n') || (c == '\t')) x = 0;
    }
#endif
    pm[i] = x;
  }

  /* limit to 7 blocks, because of dot map not fully done */
  n = BLOCK_COUNT * block_size;
  if (n > plain_mf.size) n = plain_mf.size;

#if 0 /* debug */
  /* print plain file using map */
  for (i = 0; i < n; ++i)
  {
    uint8_t c = ' ';
    if (pm[i]) c = plain_mf.base[i];
    printf("%c", c);
  }
  printf("\n");
  getchar();
#endif /* debug */

  /* catch sigint */
  signal(SIGINT, on_sigint);

  /* recover a, z */
  recover_az(cipher_mf.base, plain_mf.base, pm, n, a, am, z, zm);

  /* decrypt cipher text */
  p = malloc(cipher_mf.size);
  memset(p, 0, cipher_mf.size);
  transform2(p, pm, cipher_mf.base, cipher_mf.size, a, am, z, zm);

  for (i = 0; i < cipher_mf.size; ++i)
  {
    if (pm[i] == 0) printf(" ");
    else printf("%c", p[i]);
  }

  printf("\n");
  free(p);
  free(pm);

  unmap_file(&cipher_mf);
  unmap_file(&plain_mf);
  unmap_file(&map_mf);

  return 0;
}
