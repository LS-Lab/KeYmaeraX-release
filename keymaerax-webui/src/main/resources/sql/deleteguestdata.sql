delete from models where userId in (select email from users where level=3);
delete from users where level=3