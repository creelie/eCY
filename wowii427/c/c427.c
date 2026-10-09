/* WOWII 427 under two readings: i(G) <= |E(X, V-X)| + floor((2/3)|E(G[V-N(P)])|), P = pendants,
   X = center (reading C) or X = maximum-degree vertices (reading M).
   Input: connected graphs in graph6 format, e.g.  for n in 4 5 6 7 8 9 10; do geng -cq $n; done | ./c427
   Output: every violating graph under each reading, then the counts per order n. */
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#define MAXN 12
typedef uint32_t U;
static int n; static U adj[MAXN];
static int parse(const char*s){ n=s[0]-63; if(n<1||n>MAXN) return 0; memset(adj,0,sizeof adj); int bit=0;
  for(int j=1;j<n;j++){ for(int i=0;i<j;i++){ int byte=1+bit/6, sh=5-bit%6; if(((s[byte]-63)>>sh)&1){ adj[i]|=1u<<j; adj[j]|=1u<<i; } bit++; } } return 1; }
int main(void){ char line[256]; long long g=0, tC=0, vC=0, vM=0, vBoth=0, gn[MAXN+1]={0}, vCn[MAXN+1]={0}, vMn[MAXN+1]={0};
  while(fgets(line,sizeof line,stdin)){ int L=strlen(line); while(L&&(line[L-1]=='\n'||line[L-1]=='\r')) line[--L]=0; if(!L||!parse(line)||n<4) continue;
    U full=(1u<<n)-1; int ecc[MAXN], conn=1, rad=99, Delta=0;
    for(int v=0;v<n;v++){ U seen=1u<<v, fr=seen; int d=0; while(fr){ U nx=0; for(U t=fr;t;t&=t-1) nx|=adj[__builtin_ctz(t)]; nx&=~seen; if(!nx) break; d++; seen|=nx; fr=nx; }
      if(seen!=full) conn=0; ecc[v]=d; if(d<rad) rad=d; int dg=__builtin_popcount(adj[v]); if(dg>Delta) Delta=dg; }
    if(!conn) continue; g++; gn[n]++;
    U C=0, M=0, P=0, NP=0; for(int v=0;v<n;v++){ if(ecc[v]==rad) C|=1u<<v; int dg=__builtin_popcount(adj[v]); if(dg==Delta) M|=1u<<v; if(dg==1) P|=1u<<v; }
    for(U t=P;t;t&=t-1) NP|=adj[__builtin_ctz(t)];
    U W=full&~NP; int eW=0; for(U t=W;t;t&=t-1) eW+=__builtin_popcount(adj[__builtin_ctz(t)]&W); eW/=2;
    int cutC=0, cutM=0; for(U t=C;t;t&=t-1) cutC+=__builtin_popcount(adj[__builtin_ctz(t)]&~C); for(U t=M;t;t&=t-1) cutM+=__builtin_popcount(adj[__builtin_ctz(t)]&~M);
    int rC=cutC+(2*eW)/3, rM=cutM+(2*eW)/3;
    /* independent domination number */
    int gi=99; for(U X=1;X<=full;X++){ int k=__builtin_popcount(X); if(k>=gi) continue; U c=X; int ind=1; for(U t=X;t;t&=t-1){ int v=__builtin_ctz(t); if(adj[v]&X){ind=0;break;} c|=adj[v]; } if(ind&&c==full) gi=k; }
    tC++; int a=gi>rC, b=gi>rM; vC+=a; vM+=b; vBoth+=a&&b; vCn[n]+=a; vMn[n]+=b;
    if(a) printf("VIOLATION-CENTER %s n=%d i=%d rhs=%d\n",line,n,gi,rC);
    if(b) printf("VIOLATION-MAXDEG %s n=%d i=%d rhs=%d\n",line,n,gi,rM); }
  for(int k=0;k<=MAXN;k++) if(gn[k]) printf("n=%d graphs=%lld violations(C=center)=%lld violations(C=M)=%lld\n",k,gn[k],vCn[k],vMn[k]);
  printf("graphs %lld violations(C=center) %lld violations(C=M) %lld both %lld\n",g,vC,vM,vBoth); return 0; }
