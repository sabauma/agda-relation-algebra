# Relational Algebra in Agda
## By Spenser Bauman

This project consists of an Agda definition of relational algebra operations along
with a means for communicating with an SQLite database.
To see the examples, compile and run example.agda.

# DataTypes.agda

This module defines a data type that is designed to mirror SQL data types along
with some types to describe database structure.
These include the definition of a database schema, a table, and a row data type
which encodes results from the database.

* U -- The universe of SQL types.
* Schema -- A list of column names and their corresponding types.
* Row -- A type family mapping a schema to a list like representation that
  stores results from the database.

Finally, this module also provides a mapping which encodes SQL types into their
corresponding Agda Types.

# Parse.agda

The database interface provides results in the form of a string which must be
parsed into a row data type corresponding to the schema of the database.
This module provides a generic parser which used a specification of a data
format to parse the input.
Using this, the module includes functionality that maps a schema to its
corresponding format that is expected from the database and functionality
to translate the parser output to the corresponding Row datatype.

# RA.agda

This module defines the relational algebra data types along with a function to
compile a relational algebra statement into it SQL equivalent.
This module also includes the functions needed to interact with the database.
In particular, the functions to generate handles to database tables along with
executing queries and parsing the results.

RA statements are parameterized by the handles they need to actually read the
database.
A handle can only be created by a function which validates a schema before
producing the handle.
The constructor for the Handle datatype is hidden to prevent the construction of
erroneous, unverified handles.
Finally, it exports a function which executes RA statements on the database and
returns a table of results.

The database compunction is provided by the Database.hs using Agda's FFI.

# Database.hs

Provides functionality to send queries (as strings of SQL statements) to the SQL
database and returns a string representation of the results.
This module can also be used to get a string representation of a table's schema.

# example.agda

Contains a series of examples of the database functionality.
This module must be compiled to produce understandable results.
It performs a series of queries on the Cars table of test.db database.
