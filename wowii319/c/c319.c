/* WOWII 318/319/320 (well total domination) under both readings of dist_even(v):
   I = v counted (distance 0 is even), X = v not counted.
   Input: graphs in graph6 format (e.g. geng -cq 10 | ./c319). Graphs that are disconnected are skipped.
   Output: up to five violating graphs per reading, then for each reading the number of graphs that
   satisfy the hypothesis ("tested") and how many of them are not well totally dominated. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXN 16
static int n, m; static uint32_t adj[MAXN];
static int parse(const char*s){ n=s[0]-63; if(n<1||n>MAXN) return 0; memset(adj,0,sizeof adj); m=0; int bit=0;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ int byte=1+bit/6, sh=5-bit%6; if(((s[byte]-63)>>sh)&1){adj[i]|=1u<<j; adj[j]|=1u<<i; m++;} bit++; } return 1; }
static uint32_t *nbO;
int main(void){
  nbO = malloc(sizeof(uint32_t)<<MAXN);
  char line[256]; long long tested[6]={0}, viol[6]={0}, graphs=0;
  const char *name[6]={"318I","318X","319I","319X","320I","320X"};
  while(fgets(line,sizeof line,stdin)){
    int L=strlen(line); while(L&&(line[L-1]=='\n'||line[L-1]=='\r')) line[--L]=0; if(!L||!parse(line)||n<2) continue; graphs++;
    int evI=0, evX=0; long long Tmin=1LL<<40; int conn=1;
    for(int v=0;v<n;v++){ uint32_t seen=1u<<v, fr=seen; int d=0, e=1; long long T=0;
      while(fr){ uint32_t nx=0; for(uint32_t t=fr;t;t&=t-1) nx|=adj[__builtin_ctz(t)]; nx&=~seen; if(!nx) break; d++; seen|=nx; fr=nx;
        T += (long long)d*__builtin_popcount(nx); if(d%2==0) e+=__builtin_popcount(nx); }
      if(seen != ((n==32)?~0u:((1u<<n)-1))) conn=0;
      if(e>evI) evI=e; if(e-1>evX) evX=e-1; if(T<Tmin) Tmin=T; }
    if(!conn) continue;
    int mC = n*(n-1)/2 - m;
    int need[6]; need[0]=evI>=mC; need[1]=evX>=mC; need[4]=evI==Tmin; need[5]=evX==Tmin;
    need[2]=need[3]=0;
    uint32_t full=(1u<<n)-1; int gd=99;
    /* gamma only if it can matter */
    { int lim = evI>evX?evI:evX; 
      for(uint32_t S=1;S<=full;S++){ int k=__builtin_popcount(S); if(k>lim||k>=gd) continue; uint32_t c=S; for(uint32_t t=S;t;t&=t-1) c|=adj[__builtin_ctz(t)]; if(c==full) gd=k; } }
    need[2]= (evI==gd); need[3]= (evX==gd);
    int any=0; for(int i=0;i<6;i++) any|=need[i]; if(!any) continue;
    nbO[0]=0; int gt=99;
    for(uint32_t S=1;S<=full;S++){ uint32_t low=S&-S; nbO[S]=nbO[S^low]|adj[__builtin_ctz(low)]; if(nbO[S]==full){int k=__builtin_popcount(S); if(k<gt) gt=k;} }
    int wtd=1; for(uint32_t S=1;S<=full&&wtd;S++){ if(nbO[S]!=full) continue; int minimal=1; for(uint32_t t=S;t;t&=t-1) if(nbO[S&~(t&-t)]==full){minimal=0;break;} if(minimal && __builtin_popcount(S)!=gt) wtd=0; }
    for(int i=0;i<6;i++) if(need[i]){ tested[i]++; if(!wtd){ viol[i]++; if(viol[i]<=5) printf("C%s %s n=%d evI=%d evX=%d gamma=%d mC=%d Tmin=%lld gt=%d\n",name[i],line,n,evI,evX,gd,mC,Tmin,gt);} }
  }
  printf("graphs %lld\n",graphs); for(int i=0;i<6;i++) printf("C%s tested %lld violations %lld\n",name[i],tested[i],viol[i]);
  return 0; }
