data<-read.csv("/Users/scott/Documents/schoolwork/cs261/finalproject/eval.csv")

pdf("plots.pdf",height=6,width=12)
par(mfrow=c(1,2))
baseline<-(data[1:3]/1000000)
stripchart(baseline, method="jitter", jitter=.05, vertical=TRUE, ylim=c(0,0.4), main="authorization check only", ylab="Millions of CPU cycles", group.names=c("envid2env", "simple attestation", "delegation"))
destroy<-(data[4:6]/1000000)
stripchart(destroy, method="jitter", jitter=.05, vertical=TRUE, ylim=c(10,14), main="sys_env_destroy", ylab="Millions of CPU cycles", group.names=c("envid2env", "simple attestation", "delegation"))
dev.off()