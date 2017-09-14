DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
if [ "$#" -eq 2 ];
then
    nuXmv -cpp -bmc -bmc_length $1 -source $DIR/nuXmv_commands.txt $2
else
    nuXmv -cpp -source $DIR/nuXmv_commands.txt $1
fi
