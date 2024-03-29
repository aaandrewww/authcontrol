data<-read.csv("/Users/scott/Documents/schoolwork/cs261/finalproject/eval.csv")

pdf("plots.pdf",height=3,width=9)
par(mfrow=c(1,3))
baseline<-(data[1:3]/1000000)
stripchart(baseline, method="jitter", jitter=.05, vertical=TRUE, ylim=c(0,0.4), main="authorization check only", ylab="Millions of CPU cycles", group.names=c("envid2env", "simple attestation", "delegation"))
destroy<-(data[4:6]/1000000)
stripchart(destroy, method="jitter", jitter=.05, vertical=TRUE, ylim=c(10,14), main="sys_env_destroy", group.names=c("envid2env", "simple attestation", "delegation"))
map<-(data[7:9]/1000000)
stripchart(map, method="jitter", jitter=.05, vertical=TRUE, ylim=c(0,0.4), main="Mapping 1000 pages", group.names=c("Caching", "No caching", "Using IPC"))
dev.off()