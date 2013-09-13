// pktsoup.c - created september 1997 carl austin bennett 1:249/116 kingston
// converts netmail, echomail, downlink's outbound files to soup for internet
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <io.h>
#include <fcntl.h>
#include <sys\types.h>
#include <sys\stat.h>
#include <ctype.h>
#include <process.h>

#ifdef MS_DOS                 //handle findfirst/findnext differently if DOS
#include <dos.h>
#define FALSE 0
#define TRUE (!FALSE)
#else
#include <os2.h>
#endif

#define BLKSIZE 1024

//global error flag for *.msg write
int err=0;

//global variables read from soupbox.cfg for souppkt & pktsoup conversion
char email[40];           //soup area tagname to strip from/add to e-mail
int nb=0;                 //# of binaries hierarchies & special handler progs
char bin[10][60];         //root name of binary groups to send to decode.cmd
char decoder[10][40];     //names of programs to store or decode binaries
int nd=0;                 //# of defined ftn destinations/domain names
char domain[40][60];      //domain to put in "from:user@domain" for pktsoup.c
struct FADDR
 {short zone,net,node,point;}
 org, dest[40];            //fido-style *.pkt source & destination addresses
unsigned long split=12345; //split long soup->ftn messages (souppkt.c only)
char reply[80],tz[40];     //path to outbound ftn packet and name of timezone
int ne=0;                  //number of e-mail attach downlinks
char encoder[10][40],      //program to encode e-mail attach packets
     eheader[10][40],      //header to prepend to encoded e-mail
     epacket[10][60];      //files to send as encoded e-mail
int nr=0;                  //number of user replace/replaceall/alias addresses
char addr0[40][50],
     addr1[40][50],
     reptype[40];
#define ALIAS 1
#define REPLACE 2
#define REPLACEALL 3

//read soupbox.cfg configuration file - note some of these values are unused
//store result in global variables - return TRUE if successful, else FALSE
int initialize(char *file)
{
 FILE *in;
 static char line[80],tag[30],
      val1[80],val2[80],val3[80];  //one line of soupbox.cfg file

 in=fopen(file,"r");
 if (!in)
  {printf("error - unable to open soupbox.cfg");
   return FALSE;}

 while (!feof(in))
   {
    line[0]=tag[0]=val1[0]=val2[0]=val3[0]=0;
    fgets(line,sizeof(line),in);
    sscanf(line,"%s %s %s %s",tag,val1,val2,val3);
    if (!stricmp(tag,"Origin"))
        sscanf(val1,"%d:%d/%d.%d",&org.zone,&org.net,&org.node,&org.point);
    if (!stricmp(tag,"Domain"))
     {
        sscanf(val1,"%d:%d/%d.%d",&dest[nd].zone,&dest[nd].net,&dest[nd].node,&dest[nd].point);
        strcpy(domain[nd],val2);
        nd++;
      }
    if (!stricmp(tag,"e-mail"))
         strcpy(email,val1);
    if (!stricmp(tag,"Split"))
         sscanf(val1,"%ld",&split);
    if (!stricmp(tag,"Encode"))
     {
        strcpy(encoder[ne],val1);       //name of encoder program
        strcpy(eheader[ne],val2);       //header for e-mail attach
        strcpy(epacket[ne],val3);       //packets to send via e-mail attach
        ne++;
      }
    if (!stricmp(tag,"Decode"))
     {
        strcpy(decoder[nb],val1);
        strcpy(bin[nb],val2);
        nb++;
      }
    if (!stricmp(tag,"Alias"))
     {
        strcpy(addr0[nr],val1);       //address on BBS for this user
        strcpy(addr1[nr],val2);       //address to use on internet
        reptype[nr]=ALIAS;
        nr++;
      }
    if (!stricmp(tag,"Replace"))
     {
        strcpy(addr0[nr],val1);       //address on BBS for this user
        strcpy(addr1[nr],val2);       //address to use on internet
        reptype[nr]=REPLACE;
        nr++;
      }
    if (!stricmp(tag,"ReplaceAll"))
     {
        strcpy(addr0[nr],val1);       //address on BBS for this user
        strcpy(addr1[nr],val2);       //address to use on internet
        reptype[nr]=REPLACEALL;
        nr++;
      }
    if (!stricmp(tag,"Reply"))
        strcpy(reply,val1);
    if (!stricmp(tag,"TimeZone"))
         strcpy(tz,val1);
   }
 fclose(in);

 if (!nd)
 {
   printf("error - no fido destination address & domain name in config file\n");
   return FALSE;
 }

 //TO DO: check config. values for validity
 return TRUE;
}

//pktsoup.c-specific section

#define writes(f,s) write(f,s,strlen(s))

//read one null-terminated string from file
void readst(int file,char str[],int maxlen)
{
 int p=0;
 unsigned char c;
 do
 {
   c=0;
   read(file,&c,1);
   if (p<maxlen)
      str[p++]=c;
 }
 while (c);
 str[maxlen-1]=0;
}

//convert one message from FTN to SOUP
int cvtmsg(int pkt,int news,int mail)
{
  static char date[60],to[60],from[90],subj[80],area[60]; //ftn header info
  static char ftnfrom[50];                       //unconverted ftn username
  unsigned ozone=0,onet=0,onode=0,opoint=0;      //ftn user address
  static char msgid[90],nul[40];
  int file=news;        //file == mail or == news, based on AREA: tag
  int i,j,rc=0;
  static unsigned char c,flag,last5[5];

  unsigned long psn,len;//message length in *.msg file
  unsigned char slen[4];

  static unsigned int ftnaddr[6]; //fido-style (ftsc001) addresses for this msg

  read(pkt,&rc,2);      //check for EOF
  if (rc!=2)
     return FALSE;

  read(pkt,ftnaddr,12);     //get ftn addresses/attribs for this msg
  readst(pkt,date,20);
  readst(pkt,to,36);
  readst(pkt,from,36);
  readst(pkt,subj,72);
  strcpy(ftnfrom,from);

  //get ftn AREA: tag, if any
  psn=lseek(pkt,0,SEEK_CUR);
  read(pkt,area,5);
  if (!!memcmp(area,"AREA:",5))  //if netmail, gate to mail.msg
  {
    file=mail;
    lseek(pkt,psn,SEEK_SET);
    area[0]=0;
  }
  else                          //else get ftn AREA: tag
  {
    i=0;
    do
    {
      read(pkt,&area[i],1);
      area[i]=tolower(area[i]);
      i++;
    }
    while (area[i-1] != '\r' && i<80);
    area[i-1]=0;
  }
  if (!strcmp(area,email))
    file=mail;
  printf("area=%s\n",area);

  //get sender's address using MSGID INTL or FMPT kludges if present
  ozone=onet=onode=opoint=0;
  psn=lseek(pkt,0,SEEK_CUR);   //remember start posn of kludges/msgbody
  do
  {
    j=0;
    do                          //read one "kludge" line
    {
      read(pkt,&msgid[j],1);j++;
     } while (msgid[j-1]!='\r' && msgid[j-1]!=0 && j<80);
     msgid[j]=0;
     if (!memicmp(msgid,"\001MSGID: ",8))   //get z:n/n.p from MSGID
       sscanf(msgid+8,"%d:%d/%d.%d",&ozone,&onet,&onode,&opoint);
     if (!memicmp(msgid,"\001FMPT ",6))     //get .p from FMPT
       sscanf(msgid+6,"%d",&opoint);
     if (!memicmp(msgid,"\001INTL ",6))     //get z:n/n from INTL
       sscanf(msgid+6,"%s %d:%d/%d",&nul,&ozone,&onet,&onode);
  } while (msgid[0]!='\r' && msgid[j-1]!=0);

  lseek(pkt,psn,SEEK_SET);     //restore .pkt file pointer
  if (ozone==0) ozone=org.zone; //use ftsc001 address if no kludges found
  if (onet==0) onet=ftnaddr[2];
  if (onode==0) onode=ftnaddr[0];

  //convert from: to first.lastname@domain.org format
  flag=FALSE;
  //set flag==TRUE if no conversion needed
  for (i=0;i<strlen(from);i++)
    {
     if (from[i]==' ') from[i]='.';
     else from[i]=tolower(from[i]);
     flag |= (from[i]=='@');
    }

  //else add BBS domain name - use first one as default if not found
  if (!flag)
    {
     for (i=0;i<nd && (ozone!=dest[i].zone || onet!=dest[i].net ||
          onode!=dest[i].node || opoint!=dest[i].point );i++);
     if (i==nd) i=0;
     strcat(from,"@");
     strcat(from,domain[i]);
    }

  //replace first.last@domain.org with address for individual user, if any
  for (i=0;i<nr;i++)
    if (!stricmp(addr0[i],from))
       if (reptype[i]==REPLACEALL || (reptype[i]==REPLACE && file==mail))
         {
          strcpy(from,addr1[i]);
          break;
         }

  if (!flag)                 //then add screen name if from field converted OK
  {
     strcat(from," (");
     strcat(from,ftnfrom);
     strcat(from,")");
  }

  printf("from: %s %d:%d/%d.%d\n",from,ozone,onet,onode,opoint);

  //change "9x" to "199x" date: (not y2k compliant - 01 Jan 10 left unchanged)
  if (date[6]==' ' && date[7]=='9')
    {
     memmove(date+9,date+7,strlen(date)-6);
     date[7]='1';
     date[8]='9';
    }
  else if (date[6]==' ' && date[7]=='0')
    {
     memmove(date+9,date+7,strlen(date)-6);
     date[7]='2';
     date[8]='0';
    }

  //remove double blank from date/time
  for (j=1;j<strlen(date);j++)
    if (date[j-1]==' ' && date[j]==' ')
      memmove(date+j,date+j+1,strlen(date)-j+1);
   //append timezone
   strcat(date," ");
   strcat(date,tz);

  //use date to generate msgid (not currently used)
  j=0;
  msgid[j++]='<';
  for (i=0;i<strlen(date);i++)
    if (date[i]>='0' && date[i]<='9')
       msgid[j++]=date[i];
  msgid[j++]='@';
  msgid[j++]=0;
  strcat(msgid,domain[0]);
  strcat(msgid,">");

  //create SOUP *.msg output
  psn=lseek(file,0,SEEK_CUR);   //allocate space for msglength
  len=0;
  write(file,"\0\0\0\0",4);

  //create usenet or e-mail headers
  if (file==mail && !!stricmp(to,"UUCP"))
  {
    len += writes(file,"To: ");
    len += writes(file,to);
    len += write(file,"\n",1);
  }
  len += writes(file,"From: ");
  len += writes(file,from);
  len += write(file,"\n",1);
  if (file==news)
  {
    len += writes(file,"Newsgroups: ");
    len += writes(file,area);
    len += write(file,"\n",1);
  }
  len += writes(file,"Subject: ");
  len += writes(file,subj);
  len += write(file,"\n",1);
  len += writes(file,"Date: ");
  len += writes(file,date);
  len += write(file,"\n",1);

  if (file==news && !!stricmp(to,"All"))
  {
    len += writes(file,"X-To: ");
    len += writes(file,to);
    len += write(file,"\n",1);
  }

#if 0
  len += writes(file,"Message-ID: ");
  len += writes(file,msgid);
  len += write(file,"\n",1);
#endif

  //TO DO: add Organization: to header if needed, based on origin

  //write blank line (end of header) except for e-mail to: UUCP
  //where remaining header info is at start of ftn message body
  if (file==news || !!stricmp(to,"UUCP"))
     len += write(file,"\n",1);

  //copy message body, converting cr to lf
  flag=1;
  memcpy(last5,"     ",5);
  do
  {
    c=0;
    read(pkt,&c,1);

    memmove(last5,last5+1,4);    //stop conversion if tearline found
    last5[4]=c;
    if (!memcmp(last5,"\r--- ",5))
      flag=30;                   //end of message

    if (c==13) c=10;             //convert cr to lf
    if (c==1) flag=0;            //remove all ^A "kludge" lines
    if (c)
      if (flag==1)
        len+=(rc=write(file,&c,1)); //copy message body only
    if (rc<0)                    //if error writing message body
       err=rc;                   //remember it so original .pkt can be retained
    if (c==10 && flag==0) flag=1;
  }
  while (c);
  len+=write(file,"\n",1);

  //write message length
  lseek(file,psn,SEEK_SET);
  memcpy(slen,&len,4);
  write(file,&slen[3],1);
  write(file,&slen[2],1);
  write(file,&slen[1],1);
  write(file,&slen[0],1);
  lseek(file,0,SEEK_END);

  return TRUE;
}

//copie -- copy one open file to another until eof reached
//returns wrc>0 if OK, wrc== -1 on error, 0 if already at eof
int copie(int in,int out)
{
  int rc,wrc=0;
  do
  {
    static unsigned char c[BLKSIZE];
    int i;
    rc=read(in,c,(unsigned) BLKSIZE);
    if (rc>0)
      wrc=write(out,c,(unsigned) rc);
  }
  while (rc>0);
  return wrc;
}

//convert outbound mail for ftn downlinks to e-mail file attachments
void attach(int mail)
{
 int i,j;
 for (i=0;i<ne;i++)               //for each downlink
 {
   int hdr,pkt;                   //original header & encoded packet files
   int wrc;                       //return code (for write error checking)
   unsigned long pos,len=0;       //SOUP length dword
   unsigned char *plen;
#ifdef MS_DOS
   struct find_t f;               //result from findfirst/findnext (dos)
#else
   FILEFINDBUF f;                 //result from findfirst/findnext (os/2)
   unsigned pcs=FIL_STANDARD;     //pcSearch from findfirst (os2)
   HDIR hd=HDIR_SYSTEM;           //handle to directory
#endif
   int rc;                        //return code from findfirst/findnext
   char s[80];

   pos=lseek(mail,0,SEEK_CUR);    //remember output file position
#ifdef MS_DOS
   rc=_dos_findfirst(epacket[i],0,&f);
#else
   rc=DosFindFirst(epacket[i],&hd,FILE_NORMAL,&f,80,&pcs,0);
#endif
   while (!rc)
    {
      //encode one packet
#ifdef MS_DOS
      sprintf(s,"%s %s $encode$.tmp",encoder[i],f.name);
#else
      sprintf(s,"%s %s $encode$.tmp",encoder[i],f.achName);
#endif
      system(s);                     //encode epacket[] as $encode$.tmp

      //leave room for soup length dword
      write(mail,&len,4);

      //TO DO: add date to header if needed (probably not)
      //copy header - remove <cr> and ^z ms-dos control chars
      hdr=open(eheader[i],O_RDONLY);
      wrc=copie(hdr,mail);
      close(hdr);

      //copy $encode$.tmp
      pkt=open("$encode$.tmp",O_RDONLY);
      wrc=copie(pkt,mail);
      close(pkt);

      remove("$encode$.tmp");          //discard encoder output when done
      if (wrc>0)                       //remove original packet if successful
#ifdef MS_DOS
        remove(f.name);
#else
        remove(f.achName);
#endif

      //write soup message length, most significant byte first
      len=lseek(mail,0,SEEK_CUR)-pos-4;
      pos=lseek(mail,pos,SEEK_SET);
      plen=(unsigned char *)&len;
      write(mail,plen+3,1);
      write(mail,plen+2,1);
      write(mail,plen+1,1);
      write(mail,plen,1);
      lseek(mail,0,SEEK_END);
#ifdef MS_DOS
      rc=_dos_findnext(&f);
#else
      rc=DosFindNext(hd,&f,80,&pcs);
#endif
   }
#ifndef MS_DOS
  DosFindClose(hd);
#endif
 }
}

void main(void)
{
 int pkt,mail,news,rep;
 unsigned long len;

 //read config. file
 if (!initialize("soupbox.cfg"))
   return;

 //create mail and news files for soup
 err=0;
 pkt=open(reply,O_RDONLY|O_BINARY);
 mail=open("mail.msg",O_WRONLY|O_BINARY|O_CREAT,S_IREAD|S_IWRITE);
 news=open("news.msg",O_WRONLY|O_BINARY|O_CREAT,S_IREAD|S_IWRITE);

 lseek(mail,0,SEEK_END);           //skip existing soup msgs
 lseek(news,0,SEEK_END);

 lseek(pkt,58,SEEK_SET);           //skip fido pkt header
 while (cvtmsg(pkt,news,mail));    //convert messages

 close(pkt);
 if (!err)                         //if able to write *.msg files ok
 {
   remove(reply);      //delete original packet if successful conversion
   attach(mail);       //generate e-mail file attaches to ftn downlinks
 }
 //generate replies file and exit
 rep=open("replies",O_WRONLY|O_BINARY|O_CREAT|O_TRUNC,S_IREAD|S_IWRITE);
 len=lseek(mail,0,SEEK_END);
 if (len>4)
   write(rep,"MAIL\tmail\tb\n",12);
 len=lseek(news,0,SEEK_END);
 if (len>4)
   write(rep,"NEWS\tnews\tB\n",12);
 close(rep);
 close(mail);
 close(news);
}
