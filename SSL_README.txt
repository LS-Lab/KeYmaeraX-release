Instructions for creating a jks file from an existing certificate:

http://xacmlinfo.org/2014/06/13/how-to-keystore-creating-jks-file-from-existing-private-key-and-certificate/

Redirecting port 9000 to port 80

iptables -t nat -A PREROUTING -p tcp --dport 80 -j REDIRECT --to-port 9000
